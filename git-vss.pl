#!/usr/bin/perl

use utf8;
use strict;
use warnings;

use Encode::Byte;
use Encode::Unicode;

use DBI;
use DBD::SQLite;

use Getopt::Long;

use File::Spec;
use File::Temp qw(tmpnam tempdir);

use POSIX qw(mktime strftime);

use Win32::OLE;
use Win32::OLE::Const 'Microsoft SourceSafe';

use IO::Pipe;
use IPC::Open2;

our $dbh;
our ($opt_init, $opt_import, $opt_connect, $git_tree, $opt_newhead, $opt_nomaps);
our ($opt_dump, $opt_load, $authors_file, $filename_file);
our ($opt_rebase, $opt_nofetch, $opt_repin, $opt_undo_checkouts,
     $opt_checkout, $opt_squash, $opt_commit, $opt_master,
     $opt_sanitize);

sub usage() {
    print STDERR <<END;
Usage: git-vss [-h|--help] [--root=GIT_repository] 
       [--new-head] [--checkout] [--squash=title] [branchname]
       --rebase branchname
       --repin  branchname commit commit...
       --init [--no-mappings] [--no-fetch] branchname vss_repo log_path log_offset < mappings
       --import=path ... branchname vss_repo log_path log_offset < mappings
       --connect base_path
       (--load|--dump) [--authors=file] [--filenames=file]
       --undo-checkouts
       --sanitize-adds
END
    exit(1);
}

GetOptions(
    'help|h'         => \&usage,
    'root|C=s'       => \$git_tree,
    'init'           => \$opt_init,
    'import=s'       => \$opt_import,
    'connect'        => \$opt_connect,
    'no-mappings'    => \$opt_nomaps,
    'new-head'       => \$opt_newhead,
    'load'           => \$opt_load,
    'dump'           => \$opt_dump,
    'authors=s'      => \$authors_file,
    'filenames=s'    => \$filename_file,
    'rebase'         => \$opt_rebase,
    'no-fetch'       => \$opt_nofetch,
    'repin'          => \$opt_repin,
    'undo-checkouts' => \$opt_undo_checkouts,
    'checkout'       => \$opt_checkout,
    'commit'         => \$opt_commit,
    'squash=s'       => \$opt_squash,
    'master=s'       => \$opt_master,
    'sanitize-adds'  => \$opt_sanitize,
 ) or usage();

$opt_nofetch = 0 unless $opt_init || $opt_import;

our $base_path;
our $vss_path;
our $log_path;
our $log_offset;
our $initial_head;

our $branch_name;

our $vss;
our $vss_user;

our %vss_path_mapping;
our @vss_path_list;

# Chdir to the specified folder
$git_tree ||= ".";
chdir $git_tree;

# Path to the git repository root
my $git_dir = `git rev-parse --git-dir`;
($? == 0) or die "Bad working directory\n";
chomp $git_dir;

$git_dir = File::Spec->rel2abs($git_dir);

# Path to the working tree root
my $work_dir = $git_dir;
$work_dir =~ s/[\\\/]\.git$//;

# Add the git installation dir to the path
my $git_path = `git --exec-path`;
chomp $git_path;
$git_path =~ s/\//\\/g;

$ENV{PATH} .= ';' . $git_path;

my $win_path = $ENV{COMSPEC};
if ($win_path) {
    $win_path =~ s/[\/\\][^\/\\]+$//;
    $ENV{PATH} .= ';' . $win_path;
}

my $checkout_file = $git_dir.'/vss-checkouts';
my $squash_msg_file = $git_dir.'/vss-message';

###########################################################
# LOG SCANNING

sub fetch(\$*) {
    my ($rp, $ra) = @_;

    local $_;
    while (<$ra>) {
        return undef unless /\n$/;
        $$rp .= $_;
        s/\s+$//;
        return $_;
    }

    return undef;
}

sub scan_log($$;$$) {
    my ($processed, $log_fn, $handler, $on_error) = @_;

    my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
               $atime,$mtime,$ctime,$blksize,$blocks)
                   = stat($log_fn);

    return -1 if ($size < $processed);
    return $processed if $size == $processed;

    open FH, '<:raw', $log_fn;
    seek FH, $processed, 0;

    my $active_proc = '';
    my ($last_pos, $last_proc);

    my @actions;
    eval {
        while (defined ($_ = fetch($active_proc, FH))) {
            next if /^\s*$/;

            if (/^(\$.*\S)$/) {
                my $path = $1;
                $path =~ s/^\$//;

                defined ($_ = fetch($active_proc, FH)) or die "Incomplete block\n";
                my $ver;
                if (/^Version:\s+(\d+)/) {
                    $ver = $1;
                    defined ($_ = fetch($active_proc, FH)) or die "Incomplete block\n";
                }

                /^User:\s+(\S+)\s+Date:/ or die "Bad date line\n";
                my $user = $1;

                defined ($_ = fetch($active_proc, FH)) or die "Incomplete block\n";
                my $cmd = $_;
                my ($arg1,$arg2);

                my $entry = {
                    path => $path,
                    version => $ver,
                    user => $user,
                };

                if ($cmd =~ /^(.+) created$/) {
                    $cmd = 'Created';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^(.+) added$/) {
                    $cmd = 'Added';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^\$?(.+) deleted$/) {
                    $cmd = 'Deleted';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^\$?(.+) destroyed$/) {
                    $cmd = 'Destroyed';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^\$?(.+) purged$/) {
                    $cmd = 'Purged';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^\$?(.+) archived$/) {
                    $cmd = 'Archived';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^Restored version (\d+) to (\d+)$/) {
                    $cmd = 'Restored';
                    $entry->{name} = $2;
                    $entry->{obj_ver} = $1;
                } elsif ($cmd =~ /^\$?(.+) recovered$/) {
                    $cmd = 'Recovered';
                    $entry->{name} = $1;
                } elsif ($cmd =~ /^Labeled (.+)$/) {
                    $cmd = 'Labeled';
                    $entry->{label} = $1;
                } elsif ($cmd =~ /^\$?(.+) shared from (\$.*)\/([^\/]*)$/) {
                    $cmd = 'Shared';
                    $entry->{name} = $1;
                    $entry->{src_path} =
                        ($3 && lc(substr($1,0,length($3))) eq lc($3)) ? $2 : undef;
                } elsif ($cmd =~ /^\$?(.+) copied from (\$.*)\/([^\/]+)$/) {
                    $cmd = 'Copied';
                    $entry->{name} = $1;
                    $entry->{src_path} =
                        ($3 && lc(substr($1,0,length($3))) eq lc($3)) ? $2 : undef;
                } elsif ($cmd =~ /^\$?(.+) moved to (\$.*)$/) {
                    $cmd = 'Moved';
                    $entry->{name} = $1;
                    $entry->{move_target} = $2;
                } elsif ($cmd =~ /^(.+) renamed to (.+)$/) {
                    $cmd = 'Renamed';
                    $entry->{name} = $1;
                    $entry->{new_name} = $2;
                } elsif ($cmd =~ /^Checked in$/) {
                    $cmd = 'Checked';
                } elsif ($cmd =~ /^\$?(.+) branched$/) {
                    $cmd = 'Branched';
                    $entry->{name} = $1;
                } else {
                    die "Unknown command: $cmd\n";
                }

                $entry->{command} = $cmd;

                die "Version undefined\n" unless defined $ver;

                my $comment;

                defined ($_ = fetch($active_proc, FH)) or die "Incomplete block\n";

                while (/\S/) {
                    $comment .= $_;
                    defined ($_ = fetch($active_proc, FH)) or die "Incomplete block\n";
                }

                $comment =~ s/^Comment: // if $comment;
                $entry->{comment} = $comment;

                my $ok = $handler ? $handler->($entry) : 1;
                push @actions, $entry if $ok;

                ($last_pos, $last_proc) = ($processed, $active_proc);
                $processed += length($active_proc);
                $active_proc = '';
            } else {
                die "Invalid head line: $_\n";
            }
        }
    };
    if ($@) {
        my $err = $@;
        $active_proc = '';
        $on_error->($err, $processed) if $on_error;
        print STDERR $err;
    }
    $processed += length($active_proc);

    return wantarray ? ($processed, $last_pos, $last_proc, \@actions) : $processed;
}

###########################################################
# LOG ANALYSIS

sub matches($$) {
    my ($path, $mask) = @_;

    return 0 unless substr($path,0,length($mask)) eq $mask;
    my $c = substr($path,length($mask),1);
    return 0 if $c && $c ne '/';
    return 1;
}

sub find_git_path($) {
    my $vss_path = shift;
    my $cpath = lc($vss_path);

    for my $candidate (@vss_path_list) {
        next unless matches($cpath, $candidate);

        # Ignore list
        return undef unless defined $vss_path_mapping{$candidate};

        my $rpath = $vss_path_mapping{$candidate} . substr($vss_path, length($candidate));
        $rpath =~ s/^\/+//;
        return $rpath;
    }

    return undef;
}

sub read_log_tasks($$) {
    my ($processed, $file) = @_;

    my $handler = sub {
        my ($entry) = @_;

        # Move affects two paths, check the target one
        if (defined $entry->{move_target}) {
            die "Unsupported move into $entry->{move_target}\n"
                if defined (find_git_path $entry->{move_target})
                || grep { matches($_, $entry->{move_target}); } @vss_path_list;
        }

        # Ignore actions that are outside of the defined mappings
        defined ($entry->{git_path} = find_git_path $entry->{path})
            or return 0;

        # These commands change naming or versions, so bail out immediately
        die "Unsupported command: $entry->{path} $entry->{command} $entry->{name}\n"
            if $entry->{command} =~ /Moved|Renamed|Branched|Restored/;

        # Ignore no-op actions
        return 0 if $entry->{command} =~ /Labeled|Archived|Created/;

        return 1;
    };

    my ($rp, $lp, $lr, $lacts) = scan_log $processed, $file, $handler, sub {
        my $msg = $_[0];
        return if $msg eq "Incomplete block\n";
        die $msg;
    };

    return $rp, $lacts;
}

###########################################################
# VSS HISTORY ANALYSIS

sub get_timestamp($) {
    my $ver = shift;

    return undef unless $ver;
    my $date = $ver->{Date};

    my $str = $date->Date('yyyy-MM-dd ').$date->Time('HH:mm:ss');
    $str =~ /(\d\d\d\d)-(\d\d)-(\d\d) (\d\d):(\d\d):(\d\d)/;

    return mktime($6, $5, $4, $3, $2-1, $1-1900);
}

sub get_last_before($$) {
    my ($item, $time) = @_;

    return undef unless $item;

    my $vset = $item->Versions(VSSFLAG_HISTIGNOREFILES);
    my $enum = Win32::OLE::Enum->new($vset);
    while (defined (my $ver = $enum->Next())) {
        next if $ver->{Action} =~ /^Label/;

        return $ver if get_timestamp $ver <= $time;
    }

    return undef;
}

sub get_version_at($$) {
    my ($item, $idx) = @_;

    return undef unless $item;
    return $item->Versions(VSSFLAG_HISTIGNOREFILES)->Item($idx);
}

my $action_lookup_stmt;

# Binds a log entry to the actual VSS history
sub convert_action($) {
    my ($entry) = @_;

    # Find the item, and extract the named version
    my $vss_item = $vss->VSSItem('$'.$entry->{path})
        or die "Cannot find item \$$entry->{path}";

    my $item_version = get_version_at $vss_item, $entry->{version}
        or die "Cannot find version \$$entry->{path}:$entry->{version}\n";

    # Verify the action - it must match the logged one
    my $item_action = $item_version->{Action};
    my $item_command;
    my $pin_version;

    if ($item_action =~ /^Pinned.*to version (\d+)$/) {
        $item_command = 'Shared';
        $pin_version = $1;
    } elsif ($item_action =~ /^Unpinned/) {
        $item_command = 'Shared';
        $entry->{unpin} = 1;
    } elsif ($item_action =~ /^(\S+)/) {
        $item_command = $1;
    }

    die "Command mismatch: $item_action vs $entry->{command}\n"
        unless $item_command eq $entry->{command};

    # Check if this action is known to have been done via git-vss
    $action_lookup_stmt = $dbh->prepare(
        'SELECT vss_action FROM known_actions '.
        'WHERE vss_physid = ? AND vss_version = ? AND NOT is_imported'
        )
        unless $action_lookup_stmt;

    $action_lookup_stmt->execute(
        $item_version->{VSSItem}->{Physical},
        $item_version->{VersionNumber}
        );

    if (my $row = $action_lookup_stmt->fetchrow_arrayref()) {
        $row->[0] = $item_command 
            if $row->[0] eq 'Added' && $item_command eq 'Recovered';
    
        ($row->[0] eq $item_command)
            or die "$entry->{path}:$entry->{version} - mismatch with known '$row->[0]':\n$item_action\n";

        print STDERR "$entry->{path}:$entry->{version} - known, skipping.\n";
        return undef;
    }

    # Prepare data to add this action into the table
    $entry->{known_action_info} = [
        $item_version->{VSSItem}->{Physical},
        $item_version->{VersionNumber},
        $item_command,
        $entry->{git_path}
        ];

    # Process the action in detail
    if ($entry->{command} =~ /Deleted|Destroyed/) {
        print STDERR "del $entry->{path}/$entry->{name}\n";
        return [ 'del', $entry->{git_path}.'/'.$entry->{name}, $item_version, $entry ];
    } elsif ($entry->{command} eq 'Checked') {
        print STDERR "edit $entry->{path}:$entry->{version}\n";
        return [ 'edit', $entry->{git_path}, $item_version, $entry ];
    } else {
        my $subpath = $entry->{git_path}.'/'.$entry->{name};
        my $file_item = $item_version->{VSSItem}->Child($entry->{name})
            or die "$entry->{name} not found in $entry->{path}:$entry->{version}\n";

        if ($entry->{command} eq 'Added') {
            print STDERR "add $subpath:1\n";
            return [ 'add', $subpath, get_version_at($file_item, 1), $entry ];
        } elsif ($entry->{command} =~ /Shared|Recovered/) {
            die "Sharing/recovering a folder" 
                if $file_item->{Type} == VSSITEM_PROJECT;
        
            my $ver = $pin_version 
                ? get_version_at($file_item, $pin_version) 
                : get_last_before($file_item, get_timestamp ($item_version));

            print STDERR "share/add $subpath:$ver->{VersionNumber}\n";
            return [ 'share', $subpath, $ver, $entry, 
                     get_timestamp($item_version), 
                     ($entry->{command} eq 'Shared' ? $ver->{Username}.': ' : '') . $ver->{Comment}, 
                     $item_version->{Username} ];
        } else {
            die "Invalid command $entry->{command}\n";
        }
    }
}

###########################################################
# FILENAMES

my %canonical_dirs;
my %canonical_files;
my $get_file_stmt;
my $add_file_stmt;
my $mark_dir_stmt;

sub fetch_file_names() {
    return if $add_file_stmt;

    $add_file_stmt = $dbh->prepare('INSERT OR IGNORE INTO file_names VALUES (?, ?, ?)');
    $mark_dir_stmt = $dbh->prepare('UPDATE file_names SET is_folder = 1 WHERE key_name = ?');
    %canonical_dirs = ();
    %canonical_files = ();

    for my $line (@{$dbh->selectall_arrayref(<<QUERY)}) 
        SELECT key_name, canonical_name, is_folder FROM file_names
QUERY
    {
        if ($line->[2]) {
            $canonical_dirs{$line->[0]} = 1;
        }

        $canonical_files{$line->[0]} = $line->[1];
    }
}

sub open_file_names() {
    return if $add_file_stmt;

    $get_file_stmt = $dbh->prepare('SELECT canonical_name, is_folder FROM file_names WHERE key_name = ?');
    $add_file_stmt = $dbh->prepare('INSERT OR IGNORE INTO file_names VALUES (?, ?, ?)');
    $mark_dir_stmt = $dbh->prepare('UPDATE file_names SET is_folder = 1 WHERE key_name = ?');
    %canonical_dirs = ();
    %canonical_files = ();    
}

sub add_file_path($;$) {
    my ($new_path, $is_dir) = @_;

    my $lnew_path = lc $new_path;
    if ($canonical_files{$lnew_path}) {
        if ($is_dir && !$canonical_dirs{$lnew_path}) {
            $canonical_dirs{$lnew_path} = 1;
            $mark_dir_stmt->execute($lnew_path);
        }

        return $canonical_files{$lnew_path};
    }

    if ($get_file_stmt) {
        $get_file_stmt->execute($lnew_path);
        
        my $row = $get_file_stmt->fetchrow_arrayref();
        if ($row) {
            my ($name, $fldr) = @$row;
            
            $canonical_dirs{$lnew_path} = 1 if $fldr;
            return $canonical_files{$lnew_path} = $name;
        }
    }
    
    my $npath;
    if ($new_path =~ /^(.+)\/([^\/]+)$/) {
        my ($dir, $file) = ($1, $2);
        $npath = &add_file_path($dir, 1).'/'.$file;
    } else {
        $npath = $new_path;
    }

    $canonical_dirs{$lnew_path} = 1 if $is_dir;
    $add_file_stmt->execute($lnew_path, $npath, $is_dir||0);

    return $canonical_files{$lnew_path} = $npath;
}

sub force_file_names($$$) {
    my ($dir, $oldpath, $newpath) = @_;
    
    my @oldlist = split /\//, $oldpath;
    my @newlist = split /\//, $newpath;
    
    die "Invalid path pair: $oldpath -> $newpath\n"
        unless @oldlist == @newlist && length($oldpath) == length($newpath);
    
    while (@oldlist) {
        rename $dir.'/'.$oldlist[0], $dir.'/'.$newlist[0]
            unless $oldlist[0] eq $newlist[0];
            
        $dir .= '/'.$newlist[0];
        shift @oldlist;
        shift @newlist;
    }
}

sub sanitize_adds() {
    open_file_names();
    
    open FH, "git-diff-index --diff-filter=A HEAD |"
        or die "Could not list added files\n";
        
    while (<FH>) {
        chomp;
        /^:(\d+) (\d+) ([a-f0-9]+) ([a-f0-9]+) (A)\t(.*)$/
            or die "Bad diff line: $_";

        my ($omode, $nmode, $oblob, $nblob, $op, $name) = ($1, $2, $3, $4, $5, $6);
        my $path = add_file_path $name;
        
        unless ($path eq $name) {
            print STDERR "Invalid addition $name, must be $path\n";
            
            system 'git-update-index', '--add', '--cacheinfo', $nmode, $nblob, $path;
            ($? == 0) or die "Index update failed\n";
            
            system 'git-update-index', '--force-remove', $name;
            
            force_file_names $work_dir, $name, $path;
        }
    }
}

my %current_files;

sub load_tree_listing($) {
    my $tree = shift;

    fetch_file_names();
    %current_files = ();

    open TREE, "git ls-tree -r --name-only --full-name $tree |";
    while (<TREE>) {
        chomp;

        $current_files{lc $_} = $_;

        my $path = add_file_path $_;
        print STDERR "Filename mismatch: $_ vs canonical $path\n"
            unless $path eq $_;
    }
    close TREE;
}

###########################################################
# AUTHORS

my %author_table;

sub load_author_table() {
    $author_table{$_->[0]} = [ $_->[1], $_->[2] ]
        for @{$dbh->selectall_arrayref(<<QUERY)};
            SELECT vss_user, real_name, real_email FROM vss_users
QUERY
}

###########################################################
# GIT IMPORT

sub cache_file($$) {
    my ($item, $path) = @_;

    unless ($item && $item->{VSSItem}) {
        print STDERR " - no data, skipping\n";
        return;
    }

    unless ($item->{VSSItem}->{Type} == VSSITEM_FILE) {
        die "Trying to cache a project: $item->{VSSItem}->{Spec} as $path";
    }
    
    my $name = tmpnam();
    unlink $name;

    $item->{VSSItem}->Get($name, VSSFLAG_FORCEDIRNO);

    unless (-e $name) {
        print STDERR " - get failed, skipping\n";
        return;
    }

    my $sha = `git-hash-object -w \"$name\"`;
    chomp $sha;
    unlink $name;

    system 'git-update-index', '--add', '--cacheinfo', '0644', $sha, $path;
}

sub exec_action($\%\%\%%) {
    my ($action, $delmap, $editmap, $cleanmap, %flags) = @_;

    $action->[1] =~ s/^\/+//;
    my $path = $current_files{lc $action->[1]};

    if ($action->[0] eq 'del') {
        unless ($path) {
            print STDERR "Deleting unknown file $action->[1]\n";
            return -1; 
        }

        return 0 if $editmap->{$path} || $delmap->{$path};

        $delmap->{$path}++;

        return 2 if $flags{-no_exec};

        $cleanmap->{$path}++;

        print STDERR "Deleting $path\n";
        system 'git-update-index', '--force-remove', $path;
    } elsif ($action->[0] eq 'edit') {
        unless ($path) {
            print STDERR "Editing unknown file $action->[1] - adding\n";
            $path = $current_files{lc $action->[1]} = add_file_path $action->[1];
        }

        return 0 if $editmap->{$path} || ($flags{-no_exec} && $delmap->{$path});

        delete $delmap->{$path};
        $editmap->{$path}++;

        return 2 if $flags{-no_exec};

        print STDERR "Editing $path\n";
        cache_file $action->[2], $path;
    } elsif ($action->[0] eq 'add' || $action->[0] eq 'share') {
        $path = $current_files{lc $action->[1]} = add_file_path $action->[1] 
            unless $path;

        return 0 if $editmap->{$path} || ($flags{-no_exec} && $delmap->{$path});

        delete $delmap->{$path};
        $editmap->{$path}++ unless $action->[3]->{unpin};

        return 2 if $flags{-no_exec};

        print STDERR "Adding $path\n";
        cache_file $action->[2], $path;
    } else {
        die "Invalid action '$action->[0]'";
    }

    return 1;
}

sub run_commit_tree($$@) {
    my ($comment, $tree, @parents) = @_;
    
    my $name = tmpnam();
    open FH, '>', $name;
    print FH $comment;
    close FH;
    
    my $parents = join('', map { ' -p '.$_; } @parents);
    my $cmd = "git-commit-tree $tree $parents < \"$name\"";

    #print "$_ => $ENV{$_}\n" for keys %ENV;
    #print "$cmd\n";
    
    my $rv = `$cmd`;
    unlink $name;
    die "Could not run git-commit-tree\n" if $?;
    
    chomp $rv;
    die "Invalid result of git-commit-tree: $rv\n" unless length($rv) == 40;
    
    return $rv;
}

sub make_commit($\@) {
    my ($old_head, $ractions) = @_;

    my @commit_actions;
    my %delmap;
    my %editmap;
    my %cleanmap;

    # Find the first valid action
    my $action;
    do {
        $action = shift @$ractions or return $old_head;
    } while (exec_action($action, %delmap, %editmap, %cleanmap) <= 0);

    push @commit_actions, $action;
    
    # Main scan:
    my $user = $action->[6];
    my $time = $action->[4];
    my $comment = $action->[0] eq 'share' ? undef : $action->[5];

    my %shared_comments;

    for (my $i = 0; $i <= $#$ractions; ) {
        my $cur_action = $ractions->[$i];

        # Stop if the time range is exceeded
        $time ||= $cur_action->[4];
        last if $cur_action->[4] && ($cur_action->[4] - $time) > 3600;

        # Stop on actions of different users that clash with the current commit.
        # Otherwise skip to redo later.
        if ($cur_action->[6] ne $user) {
            last if exec_action($cur_action, %delmap, %editmap, %cleanmap, -no_exec => 1) == 0;
            $i++;
            next;
        }

        # Unpin comments are ignored;
        unless ($cur_action->[3]->{unpin}) {
            # Share actions batch comments for individual files together
            if ($cur_action->[0] eq 'share') {
                last if $comment;

                $shared_comments{$cur_action->[5]}++;
            } else {
                last if %shared_comments && $cur_action->[5];

                # Break on changing comment for ordinary updates
                $comment ||= $cur_action->[5];
                last if $cur_action->[5] && $cur_action->[5] ne $comment;
            }
        }

        # Execute the action, or stop on conflict
        last if exec_action($cur_action, %delmap, %editmap, %cleanmap) == 0;
        push @commit_actions, splice(@$ractions, $i, 1);
    }

    $comment = join("\n", sort keys %shared_comments)
        if %shared_comments;

    #delete $current_files{lc $_} for keys %cleanmap;

    # Store the tree
    my $tree_sha = `git-write-tree`;
    chomp $tree_sha;
    die "Failed to write tree: $tree_sha" unless length($tree_sha) == 40;

    # Create a commit object
    local $ENV{GIT_AUTHOR_NAME} = $author_table{lc $user}[0] || $user;
    local $ENV{GIT_AUTHOR_EMAIL} = $author_table{lc $user}[1] || $user;
    local $ENV{GIT_AUTHOR_DATE} = strftime("+0000 %Y-%m-%d %H:%M:%S",gmtime($time));
    local $ENV{GIT_COMMITTER_NAME} = $author_table{lc $user}[0] || $user;
    local $ENV{GIT_COMMITTER_EMAIL} = $author_table{lc $user}[1] || $user;
    local $ENV{GIT_COMMITTER_DATE} = strftime("+0000 %Y-%m-%d %H:%M:%S",gmtime($time));

    $comment ||= '--none--';
    
    my $sha = run_commit_tree $comment, $tree_sha, $old_head;
    
    # Log the actions into the db for future use
    $dbh->prepare(
        'INSERT OR REPLACE INTO known_commits '.
        '(commit_id, branch_name, parent_id, is_imported) '.
        'VALUES (?, ?, ?, 1)'
        )->execute(
            $sha, $branch_name, $old_head
        );

    my $ins_stmt = $dbh->prepare(
        'INSERT OR REPLACE INTO known_actions '.
        '(vss_physid, vss_version, vss_action, git_path, commit_id, is_imported) '.
        'VALUES (?, ?, ?, ?, ?, 1)'
        );

    $ins_stmt->execute(@{$_->[3]{known_action_info}}[0..3], $sha)
        for @commit_actions;

    # Done
    print STDERR " == $user $time\n";
    return $sha;
}

sub fetch_remote_head() {
    return if $base_path eq '.';

    system 'git-fetch', $base_path, '+refs/heads/'.$branch_name.':refs/remotes/vss/'.$branch_name;
    ($? == 0) or die "Could not fetch remote head.\n";
}

sub push_remote_head() {
    return if $base_path eq '.';

    system 'git-push', $base_path, $initial_head.':refs/heads/'.$branch_name;
    ($? == 0) or die "Could not push new head to the common store.\n";
}

sub set_local_head($) {
    my $head = shift;

    if ($base_path eq '.') {
        system 'git-branch', '-f', $branch_name, $head;
        ($? == 0) or die "Could not set local branch.\n";
    } else {
        my $fpath = $git_dir.'/refs/remotes/vss/'.$branch_name;
        die "Local head does not exist: $fpath" unless -f $fpath;
        
        open FH, '>:raw', $fpath;
        print FH "$head\n";
        close FH;
    }    

    $initial_head = $head;
}

sub fetch_data(%) {
    my (%flags) = @_;

    print STDERR "Fetching...\n";

    # Read the log
    my ($rp, $acts) = read_log_tasks $log_offset, $log_path;
    die "FATAL: The log was rotated.\n" if $rp < $log_offset;

    return 0 if $rp == $log_offset;

    if (@$acts) {
        # Match log entries to the VSS history
        my @cacts =
            grep { defined $_ }
            map {
                my $info = convert_action($_);
                if(defined $info && $info->[0] ne 'share') {
                    $info->[4] = get_timestamp($info->[2]) if $info->[2];
                    $info->[5] = $info->[2] ? $info->[2]->{Comment} : $info->[3]->{comment};
                    $info->[6] = $info->[2] ? $info->[2]->{Username} : $info->[3]->{user};
                }
                $info;
            } @$acts;

        my $head = $initial_head;

        # Execute commits
        if (@cacts) {
            # Use separate index file
            local $ENV{GIT_INDEX_FILE} = tmpnam();

            system 'git-read-tree', $head;
            eval {
                load_tree_listing $head;
                load_author_table;

                $head = make_commit $head, @cacts 
                    while @cacts;
            };
            my $rv = $@;
            unlink $ENV{GIT_INDEX_FILE};
            die $rv if $rv;
        }

        # Update the branch
        unless ($initial_head eq $head) {
            set_local_head($head);
            push_remote_head() unless $opt_commit;
        }
    }

    $log_offset = $rp;
    return 1;
}

sub rec_add_files(\@$$);

sub rec_add_files(\@$$) {
    my ($robjlist, $dirpath, $reppath) = @_;

    opendir DIR, $dirpath;
    my @files = readdir DIR;
    closedir DIR;

    for my $fname (@files) {
        next if $fname =~ /^\.+$/;
        next if $fname =~ /^\.(?:svn|git)$/;
        next if $fname =~ /s[sc]c$/;

        my $dirfile = $dirpath . "\\" . $fname;
        my $repfile = $reppath ? $reppath . '/' . $fname : $fname;

        if (-d $dirfile) {
            rec_add_files @$robjlist, $dirfile, $repfile;
        } else {
            my $path = add_file_path $repfile;
            print STDERR "\r$path              ";

            my $sha = `git-hash-object -w \"$dirfile\"`;
            chomp $sha;
            die "Failed to add object\n" unless length($sha) == 40;

            push @$robjlist, [ $sha, $path ];
        }
    }
}

sub create_initial_branch {
    local $ENV{GIT_INDEX_FILE} = tmpnam();

    my @objects;
    rec_add_files @objects, $opt_import, '';

    while (@objects) {
        my @part;
        if (@objects > 12) {
            @part = splice @objects, 0, 12;
        } else {
            @part = @objects;
            @objects = ();
        }

        system "git-update-index", "--add",
            map { ("--cacheinfo", "0644", $_->[0], $_->[1]); } @part;
    }

    my $tree_sha = `git-write-tree`;
    chomp $tree_sha;
    die "Failed to write tree: $tree_sha" unless length($tree_sha) == 40;

    my $sha = run_commit_tree "Initializing branch $branch_name\n", $tree_sha;

    unlink $ENV{GIT_INDEX_FILE};
    
    $dbh->prepare(
        'INSERT OR REPLACE INTO known_commits '.
        '(commit_id, branch_name, parent_id, is_imported) '.
        'VALUES (?, ?, NULL, 0)'
        )->execute(
            $sha, $branch_name
        );

    system 'git-branch', $branch_name, $sha;
    $initial_head = $sha;
}

###########################################################
# DATABASE

sub create_tables() {
    $dbh->do(<<QUERY);
        CREATE TABLE IF NOT EXISTS vss_branches (
            branch_name  TEXT NOT NULL,
            repo_path    TEXT NOT NULL,
            log_path     TEXT NOT NULL,
            current_head TEXT NOT NULL,
            log_offset   INTEGER NOT NULL,
            checkin_branch TEXT,
            PRIMARY KEY (branch_name)
        )
QUERY

    $dbh->do(<<QUERY);
        CREATE TABLE IF NOT EXISTS vss_mappings (
            branch_name  TEXT NOT NULL,
            vss_path     TEXT NOT NULL,
            git_path     TEXT,
            PRIMARY KEY (branch_name, vss_path)
        )
QUERY

    $dbh->do(<<QUERY);
        CREATE TABLE IF NOT EXISTS vss_users (
            vss_user     TEXT NOT NULL,
            real_name    TEXT NOT NULL,
            real_email   TEXT NOT NULL,
            PRIMARY KEY (vss_user)
        )
QUERY

    $dbh->do(<<QUERY);
        CREATE TABLE IF NOT EXISTS file_names (
            key_name       TEXT NOT NULL,
            canonical_name TEXT NOT NULL,
            is_folder      INTEGER NOT NULL,
            PRIMARY KEY (key_name)
        )
QUERY

    $dbh->do(<<QUERY);
        CREATE TABLE IF NOT EXISTS known_actions (
            vss_physid   TEXT NOT NULL,
            vss_version  INTEGER NOT NULL,
            vss_action   TEXT NOT NULL,
            git_path     TEXT NOT NULL,
            commit_id    TEXT NOT NULL,
            is_imported  INTEGER NOT NULL DEFAULT 1,
            PRIMARY KEY (vss_physid, vss_version)
        )
QUERY

    $dbh->do(<<QUERY);
        CREATE INDEX IF NOT EXISTS ICommitActions ON known_actions(commit_id)
QUERY

    $dbh->do(<<QUERY);
        CREATE TABLE IF NOT EXISTS known_commits (
            commit_id    TEXT NOT NULL,
            branch_name  TEXT NOT NULL,
            parent_id    TEXT,
            is_imported  INTEGER NOT NULL DEFAULT 1,
            PRIMARY KEY (commit_id)
        )
QUERY
}

sub load_mappings() {
    %vss_path_mapping = ();

    for my $line (@{$dbh->selectall_arrayref(<<QUERY)}) 
        SELECT vss_path, git_path FROM vss_mappings
        WHERE branch_name = @{[$dbh->quote($branch_name)]}
QUERY
    {
        $vss_path_mapping{lc $line->[0]} = $line->[1];
    }

    @vss_path_list = reverse sort keys %vss_path_mapping
        or die "Could not load mappings\n";
}

sub load_other_mappings($) {
    my $branch = shift;

    return undef unless $branch;

    local %vss_path_mapping;
    local @vss_path_list;
    local $branch_name = $branch;

    load_mappings();

    return { %vss_path_mapping };
}

sub import_mappings() {
    my $ist = $dbh->prepare('INSERT OR REPLACE INTO vss_mappings VALUES (?, ?, ?)');
    
    my $fh = \*STDIN;
    
    if ($ARGV[0]) {
        open $fh, $ARGV[0] 
            or die "Cannot open $ARGV[0]\n";
        shift @ARGV;
    }
    
    while (<$fh>) {
        chomp;
        next if /^\s*(?:\#.*)?$/;

        if (/^\s*(\/[^:]+[^\/:\s])\/?\s*[:=]\s*(?:\/(\S*)|(IGNORE))\s*$/) {
            my ($bpath, $rpath, $ignore) = ($1, $2||'', $3);

            $bpath =~ s/\/+$//;
            $rpath =~ s/\/+$//;
            $rpath ||= '/';

            $ist->execute($branch_name, lc $bpath, $ignore ? undef : $rpath);
        } else {
            die "Invalid path mapping: $_\n";
        }
    }
}

sub load_name_tree($;$) {
    my ($tree, $path) = @_;

    for my $item (values %$tree) {
        $item->[0] =~ s/\.([^\.]+)$/'.'.lc($1)/e
            unless %{$item->[1]};

        my $subpath = $path ? $path.'/'.$item->[0] : $item->[0];
        my $rpath = add_file_path $subpath;
        print STDERR "\rMismatch: $rpath    " unless $rpath eq $subpath;

        &load_name_tree($item->[1], $subpath);
    }
}

sub load_data() {
    if ($authors_file) {
        open DUMP, $authors_file 
            or die "Cannot open $authors_file\n";

        my $upd_stmt = $dbh->prepare('INSERT OR REPLACE INTO vss_users (vss_user, real_name, real_email) VALUES (?, ?, ?)');

        while (<DUMP>) {
            chomp;
            next if /^\s*(?:\#.*)?$/;

            /^\s*(\S+)\s*=\s*([^\<\s][^\<]+[^\<\s])\s*<\s*([^\>\s][^\>]+[^\>\s])\s*>\s*$/
                or die "Invalid user file format: $_\n";

            my ($user, $name, $email) = ($1, $2, $3);
            $upd_stmt->execute(lc $user, $name, $email);
        }

        close DUMP;
    }

    if ($filename_file) {
        open DUMP, $filename_file 
            or die "Cannot open $filename_file\n";

        my %nametable;

        while (<DUMP>) {
            chomp;
            s/^\s*\/*//;
            s/\/*\s*$//;
            next if $_ eq '';

            my $tree = \%nametable;
            for my $item (split /\//, $_) {
                my $entry = ($tree->{lc $item} ||= [$item, {}, {$item => 1}]);

                if ($entry->[0] ne $item && !$entry->[2]{$item}) {
                    $entry->[2]{$item}++;

                    my $cup = uc($entry->[0]) eq $entry->[0];
                    my $clo = lc($entry->[0]) eq $entry->[0];
                    my $nup = uc($item) eq $item || ($item =~ /\.[^\.]*[A-Z][^\.]$/);

                    if ($cup || ($clo && !$nup)) {
                        $entry->[0] = $item;
                    } else {
                        print STDERR "Old: $entry->[0], New: $item\nSwitch [y/n]? ";
                        my $rv = <STDIN>;
                        $entry->[0] = $item if $rv =~ /[Yy]/;
                    }
                }

                $tree = $entry->[1];
            }
        }

        fetch_file_names();
        load_name_tree \%nametable;

        close DUMP;
    }

    $dbh->do('COMMIT');
}

sub dump_data() {
    if ($authors_file) {
        open DUMP, '>', $authors_file;
        print DUMP "$_->[0] = $_->[1] <$_->[2]>\n"
            for @{$dbh->selectall_arrayref(<<QUERY)};
                SELECT vss_user, real_name, real_email FROM vss_users
QUERY
        close DUMP;
    }

    if ($filename_file) {
        open DUMP, '>', $filename_file;
        print DUMP "$_->[0]\n"
            for @{$dbh->selectall_arrayref(<<QUERY)};
                SELECT canonical_name FROM file_names
QUERY
        close DUMP;
    }
}

###########################################################
# CHECKING OUT

sub find_items_by_path($%) {
    my ($path, %flags) = @_;

    my @items;
    my $rmapping = $flags{-mappings} || \%vss_path_mapping;

    while (my ($vsspath, $lpath) = each %$rmapping) {
        #print "? $vsspath $lpath $path\n";
        next unless defined $lpath
            && (matches($path, $lpath) || $lpath eq '/');

        #print "? $vsspath $lpath $path\n";
        my $tail = $lpath eq '/' ? '/'.$path : substr($path, length($lpath));
            
        my $item = $vss->VSSItem(
            '$'.$vsspath.$tail
            ) or next;

        if ($flags{-physical}) {
            next unless $item->{Physical} eq $flags{-physical};
        }

        push @items, $item;
    }

    if ($flags{-force_one}) {
        (@items > 0) or
            die "No VSS paths match for $path".
                ($flags{-physical} ?
                    " (physical $flags{-physical})" :
                    '').
                "\n";
    }

    if ($flags{-force_one} || $flags{-force_noambig}) {
        (@items < 2) or
            die "Ambiguous match for $path: ".
                join(', ', map { $_->[0]->{Spec} } @items).
                "\n";
    }

    return @items;
}

sub check_conflicting_checkout($) {
    my $item = shift;

    my $costatus = $item->{IsCheckedOut};

    if ($costatus && $costatus != VSSFILE_CHECKEDOUT_ME) {
        my $couts = Win32::OLE::Enum->new($item->{Checkouts});
        my @info;

        while (defined (my $cout = $couts->Next())) {
            push @info,
                $cout->{Username}.
                ' on '.$cout->{Machine}.
                ' since '.$cout->{Date}->Date('yyyy-MM-dd');
        }

        die "File is already checked out to ".join(', ', @info).": $item->{Spec}\n";
    }
}

sub get_last_version($) {
    my ($item) = @_;
    
    return Win32::OLE::Enum->new($item->Versions())->Next();
}

sub check_pinned_to_last($;$) {
    my ($item, $new_ver) = @_;

    if ($item->{IsPinned}) {
        my $top_ver =
            defined $new_ver ? $new_ver - 1 : get_last_version($item)->{VersionNumber};

        if ($top_ver < $item->{VersionNumber}) {
            print STDERR "File $item->{Spec} already pinned to $item->{VersionNumber}\n";
        } elsif ($top_ver > $item->{VersionNumber}) {
            my %commit_info;

            $commit_info{$_->[0]} = [ $_->[1], $_->[2] ]
                for @{$dbh->selectall_arrayref(<<QUERY)};
                    SELECT vss_version, commit_id, is_imported
                    FROM known_actions
                    WHERE vss_physid = @{[$dbh->quote($item->{Physical})]}
                      AND vss_version > $item->{VersionNumber}
                      AND vss_version <= $top_ver
QUERY

            my @entries;
            for (my $ver = $item->{VersionNumber}+1; $ver <= $top_ver; $ver++)
            {
                my $info = get_version_at $item, $ver;
                push @entries,
                    $ver.': '.$info->{Username}.
                         ' ('.$info->{Date}->Date('yyyy-MM-dd').') - '.($info->{Comment}||'no comment');

                if ($commit_info{$ver}) {
                    $entries[-1] .= "\n    commit $commit_info{$ver}[0]";
                    $entries[-1] .= ' (imported)' if $commit_info{$ver}[1];
                }
            }

            die "File is pinned to version $item->{VersionNumber}, ".
                "while the latest is $top_ver: $item->{Spec}\n".
                join("\n", @entries)."\n";
        }
    }
}

sub check_within_mapping($$) {
    my ($path, $mapping) = @_;

    die "Master branch not specified for unpinned share $path\n"
        unless $mapping;

    my $lpath = lc $path;
    $lpath =~ s/^\$//;
    
    for my $testpath (keys %$mapping) {
        return if matches($lpath, $testpath);
    }

    die "Unpinned share not within master branch: $path\n";
}

sub get_checkin_spec($$) {
    my ($item, $mapping) = @_;

    my @pinned;
    my @unpinned;

    my $links = Win32::OLE::Enum->new($item->{Links});
    while (defined (my $link = $links->Next())) {
        push @pinned, $link if $link->{IsPinned};
        push @unpinned, $link if !$link->{IsPinned};
    }

    (@unpinned > 0) or
        die "File has no unpinned shares: ".
            join(', ', map { $_->{Spec} } @pinned).
            "\n";

    (@unpinned < 2) or
        die "File has multiple unpinned shares: ".
            join(', ', map { $_->{Spec} } @unpinned).
            "\n";

    check_within_mapping $unpinned[0]{Spec}, $mapping
        if $item->{IsPinned};

    return [ $unpinned[0], $item->{IsPinned} ? $item : undef ];
}

sub find_add_root($%) {
    my ($path, %flags) = @_;

    my @adds;
    for(;;) {
        my ($item) =
            find_items_by_path $path,
                    -force_noambig => 1,
                    -mappings => $flags{-mappings};

        return ($item, @adds) if $item;

        $path =~ /^(?:(.+)\/)?([^\/]+)$/ or die "Bad path: $path";
        unshift @adds, $2;
        $path = $1||'';
    }
}

sub spawn_project_tree($@) {
    my ($root, @adds) = @_;

    for my $pname (@adds) {
        my $ci = $root->Child($pname);

        $ci = $root->NewSubproject($pname, "") unless $ci;

        $root = $ci;
    }

    return $root;
}

my %checkouts;
my %checkout_adds;
my $checked_out_now = 0;
my $checkin_merge_base;
my $checkin_comment;

sub check_out_file($$) {
    my ($path, $master_map) = @_;

    return if $checkout_adds{$path};
    return if $checkouts{$path};

    my ($item) = find_items_by_path $path, -force_one => 1;

    check_conflicting_checkout $item;
    check_pinned_to_last $item;

    my $spec = get_checkin_spec $item, $master_map;

    print CHECKOUT_LOG $branch_name,"\t",$spec->[0]{Spec},"\n";

    unless ($spec->[0]{IsCheckedOut} == VSSFILE_CHECKEDOUT_ME) {
        my $phys_path = $work_dir.'/'.$path;
        $phys_path =~ s/\//\\/g;

        $checked_out_now++;
        $spec->[0]->Checkout("", $phys_path, VSSFLAG_FORCEDIRNO | VSSFLAG_GETNO);

        die "Checkout of $spec->[0]{Spec} failed.\n"
            unless $spec->[0]{IsCheckedOut} == VSSFILE_CHECKEDOUT_ME;
    }

    $checkouts{$path} = $spec;
}

sub check_out_add($$) {
    my ($path, $master_map) = @_;

    return if $checkout_adds{$path};
    die "File checked out, cannot add: $path\n" if $checkouts{$path};

    my ($root, @adds) = find_add_root $path, -mappings => $master_map;
    die "File exists in the master branch, cannot add: $path\n" unless @adds;

    my $share_spec;

    if ($master_map) {
        my ($root2, @adds2) = find_add_root $path;
        die "File exists, cannot add: $path\n" unless @adds2;

        $share_spec = [ $root2, \@adds2 ];
    }

    print CHECKOUT_LOG $branch_name,"\t",join('/', $root->{Spec}, @adds),"\n";

    $checkout_adds{$path} = [ [ $root, \@adds ], $share_spec ];
}

sub exec_repin(\@\@\@;$) {
    my ($rdellist, $rsharelist, $rpinlist, $ins_stmt) = @_;

    for my $delitem (@$rdellist) {
        my ($name, $item) = @$delitem;

        next if $item->{Deleted};

        my $parent = $item->{Parent};

        my $buddy = $parent->Child($item->{Name}, 1);
        $buddy->Destroy() if $buddy;

        $item->{Deleted} = 1;

        if ($ins_stmt) {
            my $pname = $name;
            $pname =~ s/\/[^\/]*$//;

            $ins_stmt->execute($parent->{Physical}, get_last_version($parent)->{VersionNumber}, 'Deleted', $pname);
        }
    }

    for my $sharespec (@$rsharelist) {
        my ($name, $parent, $adds, $fitem, $make_cout) = @$sharespec;

        my $fname = pop @$adds;
        $parent = spawn_project_tree $parent, @$adds;

        my $fver = $fitem->Version(1);
        $parent->Share($fver, "", VSSFLAG_GETNO);

        if ($make_cout) {
            delete $checkout_adds{$name};
            $checkouts{$name} = [ $fitem, $parent->Child($fname) ];
        }

        if ($ins_stmt) {
            my $pname = $name;
            $pname =~ s/\/[^\/]*$//;

            $ins_stmt->execute($parent->{Physical}, get_last_version($parent)->{VersionNumber}, 'Shared', $pname);
        }
    }

    for my $repin (@$rpinlist) {
        my ($name, $item, $version) = @$repin;

        next if $version <= $item->{VersionNumber};

        my $parent = $item->{Parent};
        my $ver0 = $item->Version(0);
        my $verT = $item->Version($version);

        my $pname = $name;
        $pname =~ s/\/[^\/]*$// if $ins_stmt;

        $parent->Share($ver0, "", VSSFLAG_GETNO);
        $ins_stmt->execute($parent->{Physical}, get_last_version($parent)->{VersionNumber}, 'Shared', $pname) if $ins_stmt;

        $parent->Share($verT, "", VSSFLAG_GETNO);
        $ins_stmt->execute($parent->{Physical}, get_last_version($parent)->{VersionNumber}, 'Shared', $pname) if $ins_stmt;
    }
}

my $checkin_tmpdir;

sub exec_checkin(\@\@\@$$) {
    my ($rdels, $radds, $rcheckins, $msg, $ins_stmt) = @_;

    my @pin_deletes;
    my @pin_shares;
    my @repins;

    $checkin_tmpdir = tempdir(CLEANUP => 1)
        unless $checkin_tmpdir;

    for my $delspec (@$rdels) {
        my ($name, $spec) = @$delspec;

        my $parent = $spec->[0]{Parent};

        unless ($spec->[0]{Deleted}) {
            my $buddy = $parent->Child($spec->[0]{Name}, 1);
            $buddy->Destroy() if $buddy;

            $spec->[0]{Deleted} = 1;
        } else {
            next unless $spec->[1];
        }

        if ($spec->[1]) {
            push @pin_deletes, [ $name, $spec->[1] ];
        } else {
            my $pname = $name;
            $pname =~ s/\/[^\/]*$//;

            $ins_stmt->execute($parent->{Physical}, get_last_version($parent)->{VersionNumber}, 'Deleted', $pname);
        }
    }

    for my $addspec (@$radds) {
        my ($name, $spec, $blob) = @$addspec;
        my ($parent, $adds) = @{$spec->[0]};

        my $fname = pop @$adds;
        $parent = spawn_project_tree $parent, @$adds;

        my $tmp = $checkin_tmpdir."\\".$fname;
        system "git-cat-file blob $blob > \"$tmp\"";
        ($? == 0 && -f $tmp) or die "Could not extract data";

        my $cver = get_last_version($parent)->{VersionNumber};

        my $fitem = $parent->Add($tmp, $msg,
                    VSSFLAG_FORCEDIRNO | VSSFLAG_DELNOREPLACE |
                    VSSFLAG_USERRONO | VSSFLAG_KEEPYES | 
                    VSSFLAG_GETNO);
        unlink $tmp;

        my $nver = get_last_version($parent)->{VersionNumber};

        unless ($nver > $cver) {
            print STDERR "File not added: $parent->{Spec}:$fname; $nver $cver\n";
        }

        if ($spec->[1]) {
            push @pin_shares, [ $name, $spec->[1][0], $spec->[1][1], $fitem, get_last_version($fitem)->{VersionNumber} ];
        } else {
            delete $checkout_adds{$name};
            $checkouts{$name} = [ $fitem, undef ];

            my $pname = $name;
            $pname =~ s/\/[^\/]*$//;

            $ins_stmt->execute($parent->{Physical}, $nver, 'Added', $pname) 
                unless $nver <= $cver;
        }
    }

    for my $checkin (@$rcheckins) {
        my ($name, $cout, $blob) = @$checkin;

        my $tmp = $checkin_tmpdir."\\".$blob;
        system "git-cat-file blob $blob > \"$tmp\"";
        ($? == 0 && -f $tmp) or die "Could not extract data";

        my $cver = get_last_version($cout->[0])->{VersionNumber};

        $cout->[0]->Checkin($msg, $tmp, VSSFLAG_FORCEDIRNO | VSSFLAG_KEEPYES);
        unlink $tmp;

        my $nver = get_last_version($cout->[0])->{VersionNumber};

        if ($nver > $cver) {
            if ($cout->[1]) {
                push @repins, [ $name, $cout->[1], $nver ];
            } else {
                $ins_stmt->execute($cout->[0]{Physical}, $nver, 'Checked', $name);
            }
        } else {
            print STDERR "File unchanged on check-in: $cout->[0]{Spec}\n";
        }
    }

    exec_repin @pin_deletes, @pin_shares, @repins, $ins_stmt;
}

sub repin_commit($) {
    my ($commit) = @_;

    my ($old_branch, $imported) = $dbh->selectrow_array(<<QUERY);
        SELECT branch_name, is_imported
        FROM known_commits
        WHERE commit_id = @{[$dbh->quote($commit)]}
QUERY

    die "Unknown commit $commit\n"
        unless $old_branch;

    die "Cannot repin to the same branch.\n"
        if $old_branch eq $branch_name;

    my @checkins = @{$dbh->selectall_arrayref(<<QUERY)};
        SELECT vss_physid, vss_version, vss_action, git_path
        FROM known_actions
        WHERE commit_id = @{[$dbh->quote($commit)]}
QUERY

    die "No actions known for $commit\n" unless @checkins;

    my $old_maps = load_other_mappings $old_branch;

    my @dellist;
    my @sharelist;
    my @pinlist;
    for my $row (@checkins) {
        my ($physid, $version, $action, $path) = @$row;

        if ($action =~ /Added|Deleted|Destroyed/) {
            my ($old_prj) =
                find_items_by_path $path,
                    -physical => $physid, -force_one => 1,
                    -mappings => $old_maps;

            my $old_ver = get_version_at $old_prj, $version;

            ($old_ver->{Action} =~ /^(Added|Deleted|Destroyed|Recovered) (.*)$/
             && ($1 eq $action || ($1 eq 'Recovered' && $action eq 'Added')))
                    or die "Action mismatch: $old_ver->{Action} vs $action";

            my $file = $2;
            my $fpath = $path.'/'.$file;

            if ($action eq 'Added') {
                my $fitem = $old_ver->{VSSItem}->Child($file)
                    or die "Cannot get added file item";

                my ($root, @adds) = find_add_root($fpath);

                @adds or die "Cannot add: file $fpath already exists\n";

                push @sharelist, [ $fpath, $root, \@adds, $fitem ];
            } else {
                my ($item) = find_items_by_path $fpath, -force_one => 1;

                check_pinned_to_last $item;
                
                print "Warning: going to delete file $item->{Spec}\n";
                push @dellist, [ $fpath, $item ];
            }
        } elsif ($action eq 'Checked') {
            my ($item) = find_items_by_path $path, -physical => $physid, -force_one => 1;

            next unless $item->{IsPinned};

            check_pinned_to_last $item, $version;
            push @pinlist, [ $path, $item, $version ];
        } else {
            die "Unsupported action in commit: $action";
        }
    }

    exec_repin @dellist, @sharelist, @pinlist;
}

sub checkout_delta($$;$) {
    my ($cur, $prev, $master_map) = @_;

    my $rv = `git-diff --name-status $prev $cur`;
    ($? == 0) or die "Error comparing $prev and $cur.\n";
    chomp $rv;

    for my $row (split /\n/, $rv) {
        my ($mode, $name) = split /\t/, $row;

        if ($mode eq 'M') {
            check_out_file $name, $master_map;
        } elsif ($mode eq 'A') {
            check_out_add $name, $master_map;
        } else {
            die "Unsupported change in diff $prev $cur: '$mode'\n"
        }
    }
}

sub checkin_delta($%) {
    my ($head, %flags) = @_;

    return if $head eq $initial_head;

    # Read the commit
    my $data = `git-cat-file commit $head`;
    my $hdr_end = index($data, "\n\n");

    ($hdr_end > 0) or die "Invalid commit $head\n";

    # Validate history chains
    my $refptr = index($data, "parent ".$initial_head."\n");
    ($refptr && $refptr < $hdr_end)
        or die "Commit $head is not a child of the current head\n";

    # Extract the comment
    my $msg = substr($data, $hdr_end + 2);
    $msg = $flags{-comment} if $flags{-comment};

    # Determine the set of actions to perform
    my $rv = `git-diff --raw --abbrev=40 $initial_head $head`;
    ($? == 0) or die "Error comparing $initial_head and $head.\n";
    chomp $rv;

    my @deletes;
    my @checkins;
    my @adds;
    for my $row (split /\n/, $rv) {
        $row =~ /^:(\d+) (\d+) ([a-f0-9]+) ([a-f0-9]+) ([AMD])\t(.*)$/
            or die "Bad diff line: $row";

        my ($oflags, $nflags, $oblob, $nblob, $mode, $name) = ($1, $2, $3, $4, $5, $6);

        if ($mode eq 'M') {
            my $cout = $checkouts{$name}
                or die "File not checked out in check-in: $name\n";

            push @checkins, [ $name, $cout, $nblob ];
        } elsif ($mode eq 'A') {
            my $cadds = $checkout_adds{$name}
                or die "File not prepared for adding: $name\n";

            push @adds, [ $name, $cadds, $nblob ];
        } else {
            die "Unsupported change in diff $initial_head $head: '$mode'\n"
        }
    }

    # Log the actions into the db for future use
    $dbh->prepare(
        'INSERT INTO known_commits '.
        '(commit_id, branch_name, parent_id, is_imported) '.
        'VALUES (?, ?, ?, 0)'
        )->execute(
            $head, $branch_name, $initial_head
        );

    my $ins_stmt = $dbh->prepare(
        'INSERT INTO known_actions '.
        '(vss_physid, vss_version, vss_action, git_path, commit_id, is_imported) '.
        'VALUES (?, ?, ?, ?, '.$dbh->quote($head).', 0)'
        );

    # Execute actions
    exec_checkin @deletes, @adds, @checkins, $msg, $ins_stmt;

    set_local_head $head;
}

sub checkout_changed_files() {
    $checkin_merge_base = `git-merge-base vss/$branch_name HEAD`;
    ($? == 0) or die "Error finding merge base.\n";
    chomp $checkin_merge_base;

    my $rv = `git-rev-list --reverse --parents vss/$branch_name..HEAD`;
    ($? == 0) or die "Error retrieving revisions.\n";
    chomp $rv;

    my @commits = split /\n/, $rv;
    unless (@commits) {
        undef $opt_commit;
        return;
    }

    my ($master_branch) = $dbh->selectrow_array(<<QUERY);
        SELECT checkin_branch FROM vss_branches
        WHERE branch_name = @{[$dbh->quote($branch_name)]}
QUERY

    my $master_map = load_other_mappings ($opt_master || $master_branch);

    open CHECKOUT_LOG, '>>', $checkout_file;

    my %seen_comments = ('--none--' => 1);

    my $prev = $checkin_merge_base;
    for my $crow (@commits) {
        my ($id, @parents) = split / /, $crow;

        ($opt_squash || (@parents == 1 && $parents[0] eq $prev))
            or die "Nonlinear commit chain at $crow; use --squash to merge the branch instead.\n";

        if ($opt_squash) {
            my $data = `git-cat-file commit $id`;
            my $msg = substr $data, index($data, "\n\n") + 2;

            $checkin_comment .= $msg unless $seen_comments{$msg};
            $seen_comments{$msg}++;
        } else {
            checkout_delta $id, $prev, $master_map;
        }

        $prev = $id;
    }

    checkout_delta $prev, $checkin_merge_base, $master_map if $opt_squash;

    close CHECKOUT_LOG;
}

sub undo_all_checkouts() {
    my %vss_paths;

    $vss_paths{$_->[0]} = $_->[1]
        for @{$dbh->selectall_arrayref(<<QUERY)};
            SELECT branch_name, repo_path FROM vss_branches
QUERY

    my %cout_set;

    open CHECKOUT_LOG, $checkout_file or return;
    while (<CHECKOUT_LOG>) {
        chomp;
        my ($branch, $file) = split /\t/, $_;

        $cout_set{$vss_paths{$branch}}{$file}++;
    }
    close CHECKOUT_LOG;

    local $vss_path;
    for $vss_path (keys %cout_set) {
        open_vss_link();

        for my $file (keys %{$cout_set{$vss_path}}) {
            my $item = $vss->VSSItem($file) or next;

            if ($item->{IsCheckedOut} == VSSFILE_CHECKEDOUT_ME) {
                $item->UndoCheckout(undef,
                    VSSFLAG_FORCEDIRNO | VSSFLAG_REPSKIP |
                    VSSFLAG_DELNOREPLACE | VSSFLAG_GETNO |
                    VSSFLAG_USERRONO);
            }
        }
    }

    unlink $checkout_file;
}

###########################################################
# TOP-LEVEL PROCEDURES

sub verify_current_head() {
    local $ENV{GIT_DIR} = $base_path;

    my $head = `git rev-parse $branch_name`;
    chomp $head;
    die "Could not determine current branch head.\n" unless length($head) == 40;

    if ($opt_newhead || $opt_init) {
        $initial_head = $head;
    } else {
        die "Mismatch between DB head $initial_head and Git head $head\n"
            if $head ne $initial_head;
    }
}

sub fetch_branch_info() {
    my $qname = $dbh->quote($branch_name);

    ($vss_path, $log_path, $log_offset, $initial_head) = $dbh->selectrow_array(<<QUERY)
        SELECT repo_path, log_path, log_offset, current_head FROM vss_branches
        WHERE branch_name = $qname
QUERY
        or die "Unknown VSS branch $branch_name\n";

    verify_current_head();
}

sub open_vss_link() {
    $vss_path =~ s/[\\\/]$//;

    # Connect to VSS
    $vss = Win32::OLE->new('SourceSafe', 'Close') 
        or die "Could not start VSS\n";

    $vss->Open($vss_path . "\\srcsafe.ini"); 
    $vss_user = $vss->{Username}
        or die "Could not connect to $vss_path\n";
}

sub is_unmerged() {
    my $umf = `git-ls-files -u`;
    return $umf =~ /\S/;
}

sub checkin_changes($) {
    my ($pre) = @_;

    die "Invalid context" if $ENV{GIT_INDEX_FILE};
    
    my $comment;
    if ($opt_squash) {
        if ($opt_squash eq '-') {
            open MSG_FILE, '<', $squash_msg_file
                or die "Old squash comment not found\n";
            local $/ = undef;
            $comment = <MSG_FILE>;
            close MSG_FILE;
        } else {
            my $comment = $opt_squash."\n".$checkin_comment;

            open MSG_FILE, '>', $squash_msg_file;
            print MSG_FILE $comment;
            close MSG_FILE;
        }
    }

    if ($opt_squash && !$pre) {
        system 'git', 'merge', 'vss/'.$branch_name;
        my $rc = $?>>8;

        die "Fatal merge failure.\n" if ($rc >= 2);

        if ($rc == 1) {
            system 'git', 'mergetool';
            ($? == 0) or die "Merge tool invocation failed\n";

            die "Unmerged files left\n" if is_unmerged;

            system 'git', 'commit', '-F', $squash_msg_file;
            ($? == 0) or die "Commit failed\n";
        }

        my $new_head = `git-rev-parse HEAD`;
        chomp $new_head;

        return if $new_head eq $initial_head;

        checkin_delta $new_head, -comment => $comment;
    } else {
        unless ($pre) {
            system 'git', 'rebase', '--onto', $initial_head, $checkin_merge_base;

            while ($? != 0) {
                if (is_unmerged) {
                    system 'git', 'mergetool';
                    ($? == 0) or die "Merge tool invocation failed\n";

                    die "Unmerged files left\n" if is_unmerged;

                    system 'git', 'rebase', '--continue';
                    next;
                }

                die "Fatal rebase failure\n";
            }
        }

        my $new_head = `git-rev-parse HEAD`;
        chomp $new_head;

        if ($opt_squash) {
            checkin_delta $new_head, -comment => $comment;
        } else {
            my $rv = `git-rev-list --reverse --parents $initial_head..$new_head`;
            ($? == 0) or die "Error retrieving revisions.\n";
            chomp $rv;

            my @commits = split /\n/, $rv;

            for my $crow (@commits) {
                my ($id, @parents) = split / /, $crow;

                (@parents == 1 && $parents[0] eq $initial_head)
                    or die "Nonlinear commit chain '$crow'";

                checkin_delta $id;
            }
        }
    }
}

sub update_branch_commits(%) {
    my (%flags) = @_;

    my $user_log_path = $log_path;

    $log_path = $vss_path . "\\" . $log_path
        unless $log_path =~ /^(?:[a-zA-Z]:)?[\\\/]/;

    # Import initial checkout
    if ($opt_import) {
        print STDERR "Creating branch $branch_name...\n";
        fetch_file_names();
        create_initial_branch();
    } else {
        fetch_remote_head();
    }

    # Commit, if already checked out, and immediate fast forward
    my $pre_commit =
        $opt_commit && !$checked_out_now &&
        $checkin_merge_base eq $initial_head;

    checkin_changes(1) if $pre_commit;

    # Import new changes
    my $changed = $opt_nofetch ? 0 : fetch_data();

    my $commit_error;
    if ($opt_commit) {
        eval {
            checkin_changes(0) unless $pre_commit;
            undo_all_checkouts();
        };
        $commit_error = $@;

        push_remote_head();
    }

    # Update the table
    if ($opt_init || $opt_import) {
        $dbh->prepare(<<QUERY)
            INSERT OR REPLACE 
            INTO vss_branches (branch_name, repo_path, log_path, current_head, log_offset, checkin_branch)
            VALUES (?, ?, ?, ?, ?, ?)
QUERY
            ->execute($branch_name, $vss_path, $user_log_path, $initial_head, $log_offset, $opt_master);
    } elsif ($changed || $opt_newhead || $opt_commit) {
        $dbh->prepare(<<QUERY)
            UPDATE vss_branches
            SET current_head = ?, log_offset = ?
            WHERE branch_name = ?
QUERY
            ->execute($initial_head, $log_offset, $branch_name);
    }

    if ($commit_error) {
        $dbh->do('COMMIT');
        die $commit_error;
    }

    return $changed;
}

###########################################################
# MAIN CODE

# Connect to the db
if ($opt_init || $opt_import || $opt_load || $opt_dump) {
    $base_path = `git config --get gitvss.basePath`;

    if ($?) {
        $base_path = '.';
        system 'git-config', 'gitvss.basePath', '.';
    } else {
        chomp $base_path;
        die "Init and import may only be done on the root repository.\n" 
            unless $base_path eq '.';
    } 
} elsif ($opt_connect) {
    $base_path = shift @ARGV;
    die "Bad base repository path: $base_path\n" unless -f $base_path."/gitvss.sqlite";

    system 'git-config', 'gitvss.basePath', $base_path;
} else {
    $base_path = `git config --get gitvss.basePath`;
    chomp $base_path;

    die "Cannot determine the base repository path\n" unless -f $base_path."/gitvss.sqlite";
}

$dbh = DBI->connect("dbi:SQLite:dbname=$base_path/gitvss.sqlite","","", { RaiseError => 1 });

if ($opt_sanitize) {
    sanitize_adds();
    exit 0;
} elsif ($opt_connect) {
    my @refspecs = 
        map { '+refs/heads/'.$_->[0].':refs/remotes/vss/'.$_->[0] }
        @{$dbh->selectall_arrayref(<<QUERY)};
            SELECT branch_name FROM vss_branches
QUERY

    die "No branches found\n" unless @refspecs;
    system 'git-fetch', $base_path, @refspecs;
    ($? == 0) or die "Could not fetch branches.\n";
    exit 0;
} elsif ($opt_undo_checkouts) {
    undo_all_checkouts();
    exit 0;
}

$dbh->do('BEGIN IMMEDIATE TRANSACTION');

if ($opt_load) {
    create_tables();
    load_data();
    exit 0;
} elsif ($opt_dump) {
    dump_data();
    exit 0;
}

# Determine which branch to update
if ($opt_init || $opt_import) {
    create_tables();

    $branch_name = shift @ARGV;
    $vss_path = shift @ARGV;
    $log_path = shift @ARGV;
    $log_offset = shift @ARGV;

    # Import path mappings
    import_mappings unless $opt_nomaps;

    # Compare current Git and database heads
    verify_current_head unless $opt_import;
} else {
    $branch_name = shift @ARGV;

    unless ($branch_name) {
        usage() if ($opt_rebase || $opt_repin);

        $branch_name = `git config --get gitvss.defaultBranch`;
        chomp $branch_name;

        die "Cannot determine branch to fetch.\n" unless $branch_name;
    }

    fetch_branch_info();
}

open_vss_link();
load_mappings();

if ($opt_checkout || $opt_commit) {
    checkout_changed_files();
} elsif ($opt_repin) {
    for my $comspec (@ARGV) {
        my $commit = `git-rev-parse --verify $comspec`;

        ($? == 0) or die "Invalid commit specified: $comspec\n";

        chomp $commit;
        print STDERR "Repinning $comspec...\n";
        repin_commit $commit;
    }
}

update_branch_commits();

# Done
$dbh->do('COMMIT');

# Rebase
if ($opt_rebase && !$opt_commit) {
    system 'git', 'rebase', 'vss/'.$branch_name;
}
