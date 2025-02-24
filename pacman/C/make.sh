#!/bin/sh

# We compile this in 32 bit mode, so that VMS has the same understanding
# of data types.
case $(uname -s) in
SunOS) # Verified under OpenSolaris 09/06--gcc 3.4.3
  cc -m32 -march=i386 -DVT420 -Wall -lcurses -o pm420 pacman.c
  test $? = 0 || {
    echo "$0: VT420 build failed"
    exit 1
  }

  cc -m32 -march=i386 -DVT340 -Wall -lcurses -o pm340 pacman.c
  test $? = 0 || {
    echo "$0: VT340 build failed"
    exit 1
  }
  ;;

Linux) # Linux, gcc >= 7.5.0
  CFLAGS="-DFORCE_CURSES"
# AFLAGS="-m32 -march=i686"    # Please uncomment for 32 bit support
  LDFLAGS="-lncurses -ltinfo"

  # Targetting the VT420
  cc ${AFLAGS} ${CFLAGS} -DVT420 -c -Wpedantic -o pm420.o pacman.c && \
  cc ${AFLAGS} -o pm420 pm420.o ${LDFLAGS}
  test $? = 0 || {
    echo "$0: VT420 build failed"
    exit 1
  }

  # Targetting the VT340
  cc ${AFLAGS} ${CFLAGS} -DVT340 -c -Wpedantic -o pm340.o pacman.c && \
  cc ${AFLAGS} -o pm340 pm340.o ${LDFLAGS}
  test $? = 0 || {
    echo "$0: VT340 build failed"
    exit 1
  }
  ;;
*)
  echo "`basename $0`: unsupported operating system"
  exit 1
  ;;
esac

