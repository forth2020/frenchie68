$ cc /define="VT420=1" /object=pm420.obj pacman.c
$ link pm420
$ cc /define="VT340=1" /object=pm340.obj pacman.c
$ link pm340
