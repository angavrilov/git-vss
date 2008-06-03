
all : git-vss.exe

git-vss.exe : git-vss.pl
	perlapp --force git-vss.pl
