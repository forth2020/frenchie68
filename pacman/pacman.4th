\ Disclaimer: this code is VT420 specific!
\ See https://vt100.net/mirror/mds-199909/cd3/term/vt42pupa.pdf
\ for the programmer's reference manual (PRM).
\ The code was developed under Gforth 0.7.3.
\
\ The magic incantation to start getty (as root) is:
\
\ /bin/stty -F /dev/ttyS0 38400
\ exec < /dev/ttyS0
\ exec /usr/bin/setsid -c \
\    /sbin/agetty -8 -c -s -L ttyS0 38400 vt420
\
\ You might elect to mess up with systemd's configuration.
\ I do not.

DECIMAL
MARKER wasteit

\ -------------------------------------------------------------
\ Guest Forth system dependencies,

: find79                       \ -- xt | 0; find79 <name>
  BL WORD
  DUP C@ 0= IF DROP ." Missing word name" EXIT THEN
  FIND 0= IF DROP FALSE THEN ;

: gf? [ find79 utime ] LITERAL ;      \ TRUE if GNU Forth

: IFZ7 [ gf?    ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFGF [ gf? 0= ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE

\ Following code block borrowed from GNU Forth 0.7.3 vt100.fs.
IFZ7 : pn    BASE @ SWAP DECIMAL 0 U.R BASE ! ;
IFZ7 : ;pn   [CHAR] ; EMIT pn ;
IFZ7 : ESC[  #27 EMIT [CHAR] [ EMIT ;
IFZ7 : AT-XY 1+ SWAP 1+ SWAP ESC[ pn ;pn [CHAR] H EMIT ;

\ A poor man's replacement for the ANS94 CASE construct.
VARIABLE _case

: case! _case ! ;
: case@ _case @ ;
: case? case@ = ;

\ bit #0: enable traces in entity.move
\ bit #1: enable traces in ghost.dirselect 
%00 CONSTANT debug

\ Pseudo-random number generator.
\ Using John Metcalf's Xorshift LFSRs PRNG.
\ http://www.retroprogramming.com/2017/07/
\   xorshift-pseudorandom-numbers-in-z80.html
VARIABLE seed  23741 seed !

: random ( -- N )
  seed @ DUP 7 LSHIFT XOR
  DUP 9 RSHIFT XOR
  DUP 8 LSHIFT XOR
  DUP seed ! ;

\ -------------------------------------------------------------
\ Games variables implemented as doubles so as to be able
\ to support 16 bit cell targets.
IFZ7 : 2VARIABLE VARIABLE 1 CELLS ALLOT ;
2VARIABLE hiscore
2VARIABLE score
2VARIABLE lives   \ This is clearly overkill
2VARIABLE gamlev  \ And so is this
2VARIABLE bonus   \ Semantics need clarification
2VARIABLE suptim  \ Semantics need clarification
0 VALUE pacman-addr \ An alias for entvec[0]
VARIABLE y0       \ Used by 'display-line' for inits purposes
VARIABLE serialno \ Instance number generator.

300 VALUE clkperiod \ Expressed in milliseconds

\ A clock cycle count during which pacman stays "supercharged."
100 1+ CONSTANT super-clkcycles

\ -------------------------------------------------------------
\ Grid specification.

33 CONSTANT #col
23 CONSTANT #row
#col #row * CONSTANT gridsize
CREATE grid gridsize ALLOT

\ -------------------------------------------------------------
\ Well known symbols.

CHAR T CONSTANT door
CHAR K CONSTANT cross
CHAR L CONSTANT pellet

\ -------------------------------------------------------------
\ Cursor control.

$1B CONSTANT esc

\ Turn off the cursor (VT200 control sequence).
: -cursor ( -- ) esc EMIT ." [?25l" ;

\ Turn on the cursor (VT200 control sequence).
: +cursor ( -- ) esc EMIT ." [?25h" ;

\ Turn off keyboard autorepeat (DECARM)
: -autorepeat ( -- ) esc EMIT ." [?8l" ;

\ Turn on keyboard autorepeat (DECARM)
: +autorepeat ( -- ) esc EMIT ." [?8h" ;

\ -------------------------------------------------------------
\ VT420 specific material.

\ Screen resolution is 800x400 in 80 column mode.
\ Aspect ratio is 1:1.4 (width/height).
1  CONSTANT pfn
1  CONSTANT pcn   \ First soft char at $21--do not override BL!
1  CONSTANT pe    \ Erase only new definitions
10 CONSTANT pcmw  \ Character width is 10 pixels in 80 col mode
0  CONSTANT pss   \ 80 columns, 24 lines
2  CONSTANT pt    \ Full cell
16 CONSTANT pcmh  \ Character height is 16: 6/6/4 in sixels
0  CONSTANT pcss  \ 94-charset, $20 (BL) and $7E (~) are RO
85 CONSTANT ufn   \ User font name is 'U' (argument to DSCS)

pcmh 6 /MOD SWAP 0<> ABS +
  CONSTANT nsixels \ Sixels per column
nsixels pcmw *
  CONSTANT chrdefbcnt \ Per-char definition byte count

: dscs ( -- ) ufn EMIT ;
: dcs ( -- ) esc EMIT $50 EMIT ; \ Define character set.
: st ( -- ) esc EMIT $5C EMIT ;  \ String terminator.
: semcol.emit [CHAR] ; EMIT ;

\ Ghosts are: Blinky (red), Pinky (pink), Inky (cyan)
\ and Clyde (orange). This is a monochrome rendition so that
\ effect will be lost...

CREATE softfont
\ Character "blinky", left half at $21 (!)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%110000 C, %111111 C, %1111 C, \ Column #2
%110000 C, %111111 C, %1111 C, \ Column #3
%111100 C, %111111 C, %0011 C, \ Column #4
%111100 C, %111111 C, %0011 C, \ Column #5
%111100 C, %111100 C, %1111 C, \ Column #6
%111100 C, %111100 C, %1111 C, \ Column #7
%111111 C, %111111 C, %0011 C, \ Column #8
%111111 C, %111111 C, %0011 C, \ Column #9

\ Character "blinky", right half at $22 (").
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %0011 C, \ Column #0
%111111 C, %111111 C, %0011 C, \ Column #1
%111100 C, %111100 C, %1111 C, \ Column #2
%111100 C, %111100 C, %1111 C, \ Column #3
%111100 C, %111111 C, %0011 C, \ Column #4
%111100 C, %111111 C, %0011 C, \ Column #5
%110000 C, %111111 C, %1111 C, \ Column #6
%110000 C, %111111 C, %1111 C, \ Column #7
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "cross", left half at $23 (#).
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %001111 C, %0000 C, \ Column #3 (eff. 1)
%000000 C, %001111 C, %0000 C, \ Column #4 (eff. 2)
%000000 C, %001111 C, %0000 C, \ Column #5 (eff. 3)
%000000 C, %001111 C, %0000 C, \ Column #6 (eff. 4)
%111100 C, %111111 C, %0011 C, \ Column #7 (eff. 5)
%111100 C, %111111 C, %0011 C, \ Column #8 (eff. 6)
%111100 C, %111111 C, %0011 C, \ Column #9 (eff. 7)

\ Character "cross", right half at $24 ($).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111100 C, %111111 C, %0011 C, \ Column #0 (eff. 8)
%111100 C, %111111 C, %0011 C, \ Column #1 (eff. 9)
%111100 C, %111111 C, %0011 C, \ Column #2 (eff. A)
%000000 C, %001111 C, %0000 C, \ Column #3 (eff. B)
%000000 C, %001111 C, %0000 C, \ Column #4 (eff. C)
%000000 C, %001111 C, %0000 C, \ Column #5 (eff. D)
%000000 C, %001111 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "Pacman going right", left half at $25 (%).
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%111100 C, %111111 C, %0011 C, \ Column #4 (eff. 2)
%111100 C, %111111 C, %0011 C, \ Column #5 (eff. 3)
%111111 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%110011 C, %110000 C, %1111 C, \ Column #8 (eff. 6)
%110011 C, %110000 C, %1111 C, \ Column #8 (eff. 7)

\ Character "Pacman going right", right half at $26 (&)
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%001111 C, %000000 C, %1111 C, \ Column #0 (eff. 8)
%001111 C, %000000 C, %1111 C, \ Column #1 (eff. 9)
%000011 C, %000000 C, %1111 C, \ Column #2 (eff. A)
%000011 C, %000000 C, %1111 C, \ Column #3 (eff. B)
%000000 C, %000000 C, %0000 C, \ Column #4 (eff. C)
%000000 C, %000000 C, %0000 C, \ Column #4 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #4 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #4 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "Pacman (gobbling)", left half at $27 (').
\ Left: colunm #0 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %001111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%111000 C, %111111 C, %0001 C, \ Column #4 (eff. 2)
%111000 C, %111111 C, %0001 C, \ Column #5 (eff. 3)
%111000 C, %111111 C, %0001 C, \ Column #6 (eff. 4)
%111100 C, %111111 C, %0011 C, \ Column #7 (eff. 5)
%111100 C, %111111 C, %0011 C, \ Column #8 (eff. 6)
%111100 C, %111111 C, %0011 C, \ Column #9 (eff. 7)

\ Character "Pacman (gobbling)", right half at $28 (()
\ Right: column #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111100 C, %111111 C, %0011 C, \ Column #0 (eff. 8)
%111100 C, %111111 C, %0011 C, \ Column #1 (eff. 9)
%111100 C, %111111 C, %0011 C, \ Column #2 (eff. A)
%111000 C, %111111 C, %0001 C, \ Column #3 (eff. B)
%111000 C, %111111 C, %0001 C, \ Column #4 (eff. C)
%111000 C, %111111 C, %0001 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %001111 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "Lower left corner", left half at $29 ()).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%111111 C, %000111 C, %0000 C, \ Column #4 (eff. 2)
%111111 C, %011111 C, %0000 C, \ Column #5 (eff. 3)
%111111 C, %011111 C, %0000 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %0000 C, \ Column #7 (eff. 5)
%111111 C, %111111 C, %0000 C, \ Column #8 (eff. 6)
%111111 C, %111111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "Lower left corner", right half at $2A (*).
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %0000 C, \ Column #0 (eff. 8)
%111111 C, %111111 C, %0000 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %0000 C, \ Column #2 (eff. A)
%111111 C, %111111 C, %0000 C, \ Column #3 (eff. B)
%111111 C, %111111 C, %0000 C, \ Column #4 (eff. C)
%111111 C, %111111 C, %0000 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "Lower right corner", left half at $2B (+).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%111111 C, %111111 C, %0000 C, \ Column #4 (eff. 2)
%111111 C, %111111 C, %0000 C, \ Column #5 (eff. 3)
%111111 C, %111111 C, %0000 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %0000 C, \ Column #7 (eff. 5)
%111111 C, %111111 C, %0000 C, \ Column #8 (eff. 6)
%111111 C, %111111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "Lower right corner", right half at $2C (,).
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %0000 C, \ Column #0 (eff. 8)
%111111 C, %111111 C, %0000 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %0000 C, \ Column #2 (eff. A)
%111111 C, %011111 C, %0000 C, \ Column #3 (eff. B)
%111111 C, %011111 C, %0000 C, \ Column #4 (eff. C)
%111111 C, %000111 C, %0000 C, \ Column #5 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "Horizontal bar", left half at $2D (-).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%110000 C, %111111 C, %0000 C, \ Column #4 (eff. 2)
%110000 C, %111111 C, %0000 C, \ Column #5 (eff. 3)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. 4)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. 5)
%110000 C, %111111 C, %0000 C, \ Column #8 (eff. 6)
%110000 C, %111111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "Horizontal bar", right half at $2E (.).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0 (eff. 8)
%110000 C, %111111 C, %0000 C, \ Column #1 (eff. 9)
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. A)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. B)
%110000 C, %111111 C, %0000 C, \ Column #4 (eff. C)
%110000 C, %111111 C, %0000 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "Vertical bar", left half at $2F (/).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%111111 C, %111111 C, %1111 C, \ Column #4 (eff. 2)
%111111 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%111111 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%111111 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%111111 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "Vertical bar", right half at $30 (0).
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%111111 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%111111 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%111111 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%111111 C, %111111 C, %1111 C, \ Column #5 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "Upper left corner", left half at $31 (1).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%000000 C, %111110 C, %1111 C, \ Column #4 (eff. 2)
%100000 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%100000 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%110000 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%110000 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%110000 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "Upper left corner", right half at $32 (2).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%110000 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%110000 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%110000 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%110000 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%110000 C, %111111 C, %1111 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "Upper right corner", left half at $33 (3).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%110000 C, %111111 C, %1111 C, \ Column #4 (eff. 2)
%110000 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%110000 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%110000 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%110000 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%110000 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "Upper right corner", right half at $34 (4).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%110000 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%110000 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%100000 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%100000 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%000000 C, %111110 C, %1111 C, \ Column #5 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "Power pellet", left half at $35 (5).
\ Left: colunm #0 and unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%100000 C, %011111 C, %0000 C, \ Column #2 (eff. 0)
%100000 C, %011111 C, %0000 C, \ Column #3 (eff. 1)
%111100 C, %111111 C, %0011 C, \ Column #4 (eff. 2)
%111100 C, %111111 C, %0011 C, \ Column #5 (eff. 3)
%111100 C, %111111 C, %0011 C, \ Column #6 (eff. 4)
%111100 C, %111111 C, %0011 C, \ Column #7 (eff. 5)
%111100 C, %111111 C, %0011 C, \ Column #8 (eff. 6)
%111100 C, %111111 C, %0011 C, \ Column #9 (eff. 7)

\ Character "Power pellet", right half at $36 (6).
\ Right: column #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111100 C, %111111 C, %0011 C, \ Column #0 (eff. 8)
%111100 C, %111111 C, %0011 C, \ Column #1 (eff. 9)
%111100 C, %111111 C, %0011 C, \ Column #2 (eff. A)
%111100 C, %111111 C, %0011 C, \ Column #3 (eff. B)
%111100 C, %111111 C, %0011 C, \ Column #4 (eff. C)
%111100 C, %111111 C, %0011 C, \ Column #5 (eff. D)
%100000 C, %011111 C, %0000 C, \ Column #6 (eff. E)
%100000 C, %011111 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "T down", left half at $37 (7).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0001 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0011 C, \ Column #3 (eff. 1)
%110000 C, %111111 C, %1111 C, \ Column #4 (eff. 2)
%110000 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%110000 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%110000 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%110000 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%110000 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "T down", right half at $38 (8).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%110000 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%110000 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%110000 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%110000 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%110000 C, %111111 C, %1111 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0011 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0001 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "T up", left half at $39 (9).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%111000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%111100 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%111111 C, %111111 C, %0000 C, \ Column #4 (eff. 2)
%111111 C, %111111 C, %0000 C, \ Column #5 (eff. 3)
%111111 C, %111111 C, %0000 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %0000 C, \ Column #7 (eff. 5)
%111111 C, %111111 C, %0000 C, \ Column #8 (eff. 6)
%111111 C, %111111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "T up", right half at $3A (:).
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %0000 C, \ Column #0 (eff. 8)
%111111 C, %111111 C, %0000 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %0000 C, \ Column #2 (eff. A)
%111111 C, %111111 C, %0000 C, \ Column #3 (eff. B)
%111111 C, %111111 C, %0000 C, \ Column #4 (eff. C)
%111111 C, %111111 C, %0000 C, \ Column #5 (eff. D)
%111100 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%111000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "T right", left half at $3B (;).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%111111 C, %111111 C, %1111 C, \ Column #4 (eff. 2)
%111111 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%111111 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%111111 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%111111 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "T right", right half at $3C (<).
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%111111 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%111111 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%111111 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%111111 C, %111111 C, %1111 C, \ Column #5 (eff. D)
%111100 C, %111111 C, %0011 C, \ Column #6 (eff. E)
%111000 C, %111111 C, %0001 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "T left", left half at $3D (=).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%111000 C, %111111 C, %0001 C, \ Column #2 (eff. 0)
%111100 C, %111111 C, %0011 C, \ Column #3 (eff. 1)
%111111 C, %111111 C, %1111 C, \ Column #4 (eff. 2)
%111111 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%111111 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%111111 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%111111 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%111111 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "T left", right half at $3E (>).
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%111111 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%111111 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%111111 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%111111 C, %111111 C, %1111 C, \ Column #5 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "West", left half at $3F (?).
\ Columns #0 and #1 are unsused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000110 C, %0000 C, \ Column #2 (eff. 0)
%100000 C, %011111 C, %0000 C, \ Column #3 (eff. 1)
%100000 C, %011111 C, %0000 C, \ Column #4 (eff. 2)
%110000 C, %111111 C, %0000 C, \ Column #5 (eff. 3)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. 4)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. 5)
%110000 C, %111111 C, %0000 C, \ Column #8 (eff. 6)
%110000 C, %111111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "West", right half at $40 (@).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0 (eff. 8)
%110000 C, %111111 C, %0000 C, \ Column #1 (eff. 9)
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. A)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. B)
%110000 C, %111111 C, %0000 C, \ Column #4 (eff. C)
%110000 C, %111111 C, %0000 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "East", left half at $41 (A).
\ Columns #0 and #1 are unsused.
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. 1)
%110000 C, %111111 C, %0000 C, \ Column #4 (eff. 2)
%110000 C, %111111 C, %0000 C, \ Column #5 (eff. 3)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. 4)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. 5)
%110000 C, %111111 C, %0000 C, \ Column #8 (eff. 6)
%110000 C, %111111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "East", right half at $42 (B).
\ Columns #8 and #9 are unsused.
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0 (eff. 8)
%110000 C, %111111 C, %0000 C, \ Column #1 (eff. 9)
%110000 C, %111111 C, %0000 C, \ Column #2 (eff. A)
%110000 C, %111111 C, %0000 C, \ Column #3 (eff. B)
%110000 C, %111111 C, %0000 C, \ Column #4 (eff. C)
%100000 C, %011111 C, %0000 C, \ Column #5 (eff. D)
%100000 C, %011111 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000110 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "South", left half at $43 (C).
\ Columns #0 through #3 are unsused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%111111 C, %000111 C, %0000 C, \ Column #4 (eff. 2)
%111111 C, %001111 C, %0000 C, \ Column #5 (eff. 3)
%111111 C, %011111 C, %0000 C, \ Column #6 (eff. 4)
%111111 C, %011111 C, %0000 C, \ Column #7 (eff. 5)
%111111 C, %011111 C, %0000 C, \ Column #8 (eff. 6)
%111111 C, %011111 C, %0000 C, \ Column #9 (eff. 7)

\ Character "South", right half at $44 (D).
\ Columns #6 and #9 are unsused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %011111 C, %0000 C, \ Column #0 (eff. 8)
%111111 C, %011111 C, %0000 C, \ Column #1 (eff. 9)
%111111 C, %011111 C, %0000 C, \ Column #2 (eff. A)
%111111 C, %011111 C, %0000 C, \ Column #3 (eff. B)
%111111 C, %001111 C, %0000 C, \ Column #4 (eff. C)
%111111 C, %000111 C, %0000 C, \ Column #5 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "North", left half at $45 (E).
\ Columns #0 through #3 are unsused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%111000 C, %111111 C, %1111 C, \ Column #4 (eff. 2)
%111100 C, %111111 C, %1111 C, \ Column #5 (eff. 3)
%111110 C, %111111 C, %1111 C, \ Column #6 (eff. 4)
%111110 C, %111111 C, %1111 C, \ Column #7 (eff. 5)
%111110 C, %111111 C, %1111 C, \ Column #8 (eff. 6)
%111110 C, %111111 C, %1111 C, \ Column #9 (eff. 7)

\ Character "North", right half at $46 (F).
\ Columns #6 and #9 are unsused.
\ Group A  Group B    Group C (top to bottom)
%111110 C, %111111 C, %1111 C, \ Column #0 (eff. 8)
%111110 C, %111111 C, %1111 C, \ Column #1 (eff. 9)
%111110 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%111110 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%111100 C, %111111 C, %1111 C, \ Column #4 (eff. C)
%111000 C, %111111 C, %1111 C, \ Column #5 (eff. D)
%000000 C, %000000 C, %0000 C, \ Column #6 (eff. E)
%000000 C, %000000 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "Door", left half at $47 (G).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %110000 C, %0000 C, \ Column #0
%110000 C, %110000 C, %0000 C, \ Column #1
%110000 C, %110000 C, %0000 C, \ Column #2 (eff. 0)
%110000 C, %110000 C, %0000 C, \ Column #3 (eff. 1)
%110000 C, %110000 C, %0000 C, \ Column #4 (eff. 2)
%110000 C, %110000 C, %0000 C, \ Column #5 (eff. 3)
%110000 C, %110000 C, %0000 C, \ Column #6 (eff. 4)
%110000 C, %110000 C, %0000 C, \ Column #7 (eff. 5)
%110000 C, %110000 C, %0000 C, \ Column #8 (eff. 6)
%110000 C, %110000 C, %0000 C, \ Column #9 (eff. 7)

\ Character "Door", right half at $48 (H).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %110000 C, %0000 C, \ Column #0 (eff. 8)
%110000 C, %110000 C, %0000 C, \ Column #1 (eff. 9)
%110000 C, %110000 C, %0000 C, \ Column #2 (eff. A)
%110000 C, %110000 C, %0000 C, \ Column #3 (eff. B)
%110000 C, %110000 C, %0000 C, \ Column #4 (eff. C)
%110000 C, %110000 C, %0000 C, \ Column #5 (eff. D)
%110000 C, %110000 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %110000 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %110000 C, %0000 C, \ Column #8
%110000 C, %110000 C, %0000 C, \ Column #9

\ Character "Pacman going left", left half at $49 (I).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0
%000000 C, %000000 C, %0000 C, \ Column #1
%000000 C, %000000 C, %0000 C, \ Column #2 (eff. 0)
%000000 C, %000000 C, %0000 C, \ Column #3 (eff. 1)
%000000 C, %000000 C, %0000 C, \ Column #4 (eff. 2)
%000000 C, %000000 C, %0000 C, \ Column #5 (eff. 3)
%000011 C, %000000 C, %1111 C, \ Column #6 (eff. 4)
%000011 C, %000000 C, %1111 C, \ Column #7 (eff. 5)
%001111 C, %000000 C, %1111 C, \ Column #8 (eff. 6)
%001111 C, %000000 C, %1111 C, \ Column #9 (eff. 7)

\ Character "Pacman going left", right half at $4A (J).
\ Group A  Group B    Group C (top to bottom)
%110011 C, %110000 C, %1111 C, \ Column #0 (eff. 8)
%110011 C, %110000 C, %1111 C, \ Column #1 (eff. 9)
%111111 C, %111111 C, %1111 C, \ Column #2 (eff. A)
%111111 C, %111111 C, %1111 C, \ Column #3 (eff. B)
%111100 C, %111111 C, %0011 C, \ Column #4 (eff. C)
%111100 C, %111111 C, %0011 C, \ Column #5 (eff. D)
%110000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%110000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%000000 C, %000000 C, %0000 C, \ Column #8
%000000 C, %000000 C, %0000 C, \ Column #9

\ Character "Pacman going up", left half at $4B (K).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%110000 C, %111111 C, %0001 C, \ Column #2 (eff. 0)
%110000 C, %111111 C, %0011 C, \ Column #3 (eff. 1)
%000000 C, %111100 C, %0011 C, \ Column #4 (eff. 2)
%000000 C, %111100 C, %0011 C, \ Column #5 (eff. 3)
%000000 C, %110000 C, %0111 C, \ Column #6 (eff. 4)
%000000 C, %110000 C, %0111 C, \ Column #7 (eff. 5)
%000000 C, %110000 C, %0111 C, \ Column #8 (eff. 6)
%000000 C, %110000 C, %0111 C, \ Column #9 (eff. 7)

\ Character "Pacman going up", right half at $4C (L).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %110000 C, %0111 C, \ Column #0 (eff. 8)
%000000 C, %110000 C, %0111 C, \ Column #1 (eff. 9)
%000000 C, %110000 C, %0111 C, \ Column #2 (eff. A)
%000000 C, %110000 C, %0111 C, \ Column #3 (eff. B)
%000000 C, %111100 C, %0011 C, \ Column #4 (eff. C)
%000000 C, %111100 C, %0011 C, \ Column #5 (eff. D)
%000000 C, %110011 C, %0011 C, \ Column #6 (eff. E)
%000000 C, %110011 C, %0001 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "Pacman going down", left half at $4D (M).
\ Group A  Group B    Group C (top to bottom)
%110000 C, %111111 C, %0000 C, \ Column #0
%110000 C, %111111 C, %0000 C, \ Column #1
%111000 C, %001100 C, %0000 C, \ Column #2 (eff. 0)
%111000 C, %001100 C, %0000 C, \ Column #3 (eff. 1)
%111100 C, %000011 C, %0000 C, \ Column #4 (eff. 2)
%111100 C, %000011 C, %0000 C, \ Column #5 (eff. 3)
%111110 C, %000000 C, %0000 C, \ Column #6 (eff. 4)
%111110 C, %000000 C, %0000 C, \ Column #7 (eff. 5)
%111110 C, %000000 C, %0000 C, \ Column #8 (eff. 6)
%111110 C, %000000 C, %0000 C, \ Column #9 (eff. 7)

\ Character "Pacman going down", right half at $4E (N).
\ Group A  Group B    Group C (top to bottom)
%111110 C, %000000 C, %0000 C, \ Column #0 (eff. 8)
%111110 C, %000000 C, %0000 C, \ Column #1 (eff. 9)
%111110 C, %000000 C, %0000 C, \ Column #2 (eff. A)
%111110 C, %000000 C, %0000 C, \ Column #3 (eff. B)
%111100 C, %000011 C, %0000 C, \ Column #4 (eff. C)
%111100 C, %000011 C, %0000 C, \ Column #5 (eff. D)
%111000 C, %111111 C, %0000 C, \ Column #6 (eff. E)
%111000 C, %111111 C, %0000 C, \ Column #7 (eff. F)
%110000 C, %111111 C, %0000 C, \ Column #8
%110000 C, %111111 C, %0000 C, \ Column #9

\ Character "Inky", left half at $4F (O)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%110000 C, %111111 C, %1111 C, \ Column #2
%110000 C, %111111 C, %1111 C, \ Column #3
%111100 C, %111111 C, %0011 C, \ Column #4
%111100 C, %111111 C, %0011 C, \ Column #5
%111100 C, %111100 C, %1111 C, \ Column #6
%111100 C, %111100 C, %1111 C, \ Column #7
%111111 C, %111111 C, %0011 C, \ Column #8
%111111 C, %001111 C, %0011 C, \ Column #9

\ Character "Inky", right half at $50 (P).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %001111 C, %0011 C, \ Column #0
%111111 C, %111111 C, %0011 C, \ Column #1
%111100 C, %111100 C, %1111 C, \ Column #2
%111100 C, %111100 C, %1111 C, \ Column #3
%111100 C, %111111 C, %0011 C, \ Column #4
%111100 C, %111111 C, %0011 C, \ Column #5
%110000 C, %111111 C, %1111 C, \ Column #6
%110000 C, %111111 C, %1111 C, \ Column #7
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "Pinky", left half at $51 (Q)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%110000 C, %111111 C, %1111 C, \ Column #2
%110000 C, %111111 C, %1110 C, \ Column #3
%111100 C, %011111 C, %0011 C, \ Column #4
%111100 C, %101111 C, %0011 C, \ Column #5
%111100 C, %110100 C, %1111 C, \ Column #6
%111100 C, %111100 C, %1111 C, \ Column #7
%111111 C, %111111 C, %0011 C, \ Column #8
%111111 C, %111111 C, %0011 C, \ Column #9

\ Character "Pinky", right half at $52 (R).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %0011 C, \ Column #0
%111111 C, %111111 C, %0011 C, \ Column #1
%111100 C, %111100 C, %1111 C, \ Column #2
%111100 C, %110100 C, %1111 C, \ Column #3
%111100 C, %101111 C, %0011 C, \ Column #4
%111100 C, %011111 C, %0011 C, \ Column #5
%110000 C, %111111 C, %1110 C, \ Column #6
%110000 C, %111111 C, %1111 C, \ Column #7
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "Clyde", left half at $53 (S)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %0000 C, \ Column #0 unused
%000000 C, %000000 C, %0000 C, \ Column #1 unused
%110000 C, %111111 C, %1111 C, \ Column #2
%110000 C, %110111 C, %1111 C, \ Column #3
%111100 C, %101111 C, %0011 C, \ Column #4
%111100 C, %011111 C, %0011 C, \ Column #5
%111100 C, %111100 C, %1110 C, \ Column #6
%111100 C, %111100 C, %1111 C, \ Column #7
%111111 C, %111111 C, %0011 C, \ Column #8
%111111 C, %111111 C, %0011 C, \ Column #9
   
\ Character "Clyde", right half at $54 (T).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %0011 C, \ Column #0
%111111 C, %111111 C, %0011 C, \ Column #1
%111100 C, %111100 C, %1111 C, \ Column #2
%111100 C, %111100 C, %1110 C, \ Column #3
%111100 C, %011111 C, %0011 C, \ Column #4
%111100 C, %101111 C, %0011 C, \ Column #5
%110000 C, %110111 C, %1111 C, \ Column #6
%110000 C, %111111 C, %1111 C, \ Column #7
%000000 C, %000000 C, %0000 C, \ Column #8 unused
%000000 C, %000000 C, %0000 C, \ Column #9 unused

\ Character "rBlinky", left half at $55 (U)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 unused
%111111 C, %111111 C, %1111 C, \ Column #1 unused
%001111 C, %000000 C, %0000 C, \ Column #2
%001111 C, %000000 C, %0000 C, \ Column #3
%000011 C, %000000 C, %1100 C, \ Column #4
%000011 C, %000000 C, %1100 C, \ Column #5
%000011 C, %000011 C, %0000 C, \ Column #6
%000011 C, %000011 C, %0000 C, \ Column #7
%000000 C, %000000 C, %1100 C, \ Column #8
%000000 C, %000000 C, %1100 C, \ Column #9

\ Character "rBlinky", right half at $56 (V).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %1100 C, \ Column #0
%000000 C, %000000 C, %1100 C, \ Column #1
%000011 C, %000011 C, %0000 C, \ Column #2
%000011 C, %000011 C, %0000 C, \ Column #3
%000011 C, %000000 C, %1100 C, \ Column #4
%000011 C, %000000 C, %1100 C, \ Column #5
%001111 C, %000000 C, %0000 C, \ Column #6
%001111 C, %000000 C, %0000 C, \ Column #7
%111111 C, %111111 C, %1111 C, \ Column #8 unused
%111111 C, %111111 C, %1111 C, \ Column #9 unused

\ Character "rInky", left half at $57 (W)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 unused
%111111 C, %111111 C, %1111 C, \ Column #1 unused
%001111 C, %000000 C, %0000 C, \ Column #2
%001111 C, %000000 C, %0000 C, \ Column #3
%000011 C, %000000 C, %1100 C, \ Column #4
%000011 C, %000000 C, %1100 C, \ Column #5
%000011 C, %000011 C, %0000 C, \ Column #6
%000011 C, %000011 C, %0000 C, \ Column #7
%000000 C, %000000 C, %1100 C, \ Column #8
%000000 C, %110000 C, %1100 C, \ Column #9

\ Character "rInky", right half at $58 (X).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %110000 C, %1100 C, \ Column #0
%000000 C, %000000 C, %1100 C, \ Column #1
%000011 C, %000011 C, %0000 C, \ Column #2
%000011 C, %000011 C, %0000 C, \ Column #3
%000011 C, %000000 C, %1100 C, \ Column #4
%000011 C, %000000 C, %1100 C, \ Column #5
%001111 C, %000000 C, %0000 C, \ Column #6
%001111 C, %000000 C, %0000 C, \ Column #7
%111111 C, %111111 C, %1111 C, \ Column #8 unused
%111111 C, %111111 C, %1111 C, \ Column #9 unused

\ Character "rPinky", left half at $59 (Y)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 unused
%111111 C, %111111 C, %1111 C, \ Column #1 unused
%001111 C, %000000 C, %0000 C, \ Column #2
%001111 C, %000000 C, %0001 C, \ Column #3
%000011 C, %100000 C, %1100 C, \ Column #4
%000011 C, %010000 C, %1100 C, \ Column #5
%000011 C, %001011 C, %0000 C, \ Column #6
%000011 C, %000011 C, %0000 C, \ Column #7
%000000 C, %000000 C, %1100 C, \ Column #8
%000000 C, %000000 C, %1100 C, \ Column #9

\ Character "rPinky", right half at $5A (Z).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %1100 C, \ Column #0
%000000 C, %000000 C, %1100 C, \ Column #1
%000011 C, %000011 C, %0000 C, \ Column #2
%000011 C, %001011 C, %0000 C, \ Column #3
%000011 C, %010000 C, %1100 C, \ Column #4
%000011 C, %100000 C, %1100 C, \ Column #5
%001111 C, %000000 C, %0001 C, \ Column #6
%001111 C, %000000 C, %0000 C, \ Column #7
%111111 C, %111111 C, %1111 C, \ Column #8 unused
%111111 C, %111111 C, %1111 C, \ Column #9 unused

\ Character "rClyde", left half at $5B ([)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C (top to bottom)
%111111 C, %111111 C, %1111 C, \ Column #0 unused
%111111 C, %111111 C, %1111 C, \ Column #1 unused
%001111 C, %000000 C, %0000 C, \ Column #2
%001111 C, %001000 C, %0000 C, \ Column #3
%000011 C, %010000 C, %1100 C, \ Column #4
%000011 C, %100000 C, %1100 C, \ Column #5
%000011 C, %000011 C, %0001 C, \ Column #6
%000011 C, %000011 C, %0000 C, \ Column #7
%000000 C, %000000 C, %1100 C, \ Column #8
%000000 C, %000000 C, %1100 C, \ Column #9

\ Character "rClyde", right half at $5C (\).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C (top to bottom)
%000000 C, %000000 C, %1100 C, \ Column #0
%000000 C, %000000 C, %1100 C, \ Column #1
%000011 C, %000011 C, %0000 C, \ Column #2
%000011 C, %000011 C, %0001 C, \ Column #3
%000011 C, %100000 C, %1100 C, \ Column #4
%000011 C, %010000 C, %1100 C, \ Column #5
%001111 C, %001000 C, %0000 C, \ Column #6
%001111 C, %000000 C, %0000 C, \ Column #7
%111111 C, %111111 C, %1111 C, \ Column #8 unused
%111111 C, %111111 C, %1111 C, \ Column #9 unused

\ The following is twice the number of sprites (dw characters).
HERE softfont - chrdefbcnt / CONSTANT nchars

: softfont.emit ( -- )
  nchars 0 DO           \ Iterate over character definitions
    nsixels 0 DO        \ Iterate over sixel groups
      pcmw 0 DO         \ Iterate over column definitions
        I nsixels * J + K chrdefbcnt * + softfont + C@
        [CHAR] ? + EMIT \ Emit sixel data
      LOOP
      I nsixels 1- <> IF [CHAR] / EMIT THEN \ Group delimiter
    LOOP
    nchars 1- I <> IF semcol.emit THEN \ Character delimiter
  LOOP ;

\ Same as . but without the trailing BL.
: decsend ( char -- ) 0 U.R ;

\ DECDLD spec:
\ DCS Pfn; Pcn; Pe; Pcmw; Pss; Pt; Pcmh; Pcss { Dscs
\ Sxbp1 ; Sxbp2 ;...; Sxbpn ST
: decdld ( -- ) dcs
    pfn  decsend semcol.emit  pcn  decsend semcol.emit
    pe   decsend semcol.emit  pcmw decsend semcol.emit
    pss  decsend semcol.emit  pt   decsend semcol.emit
    pcmh decsend semcol.emit  pcss decsend
    [CHAR] { EMIT dscs
    softfont.emit
  st
  \ Charset designation.
  esc EMIT [CHAR] ) EMIT dscs ; \ G1 <- <UserFontName>

\ Display doublewidth character at offset 'offs'.
\ $21 is the first user defined character in the software font.
: .dwchar ( offs -- ) $21 + DUP EMIT 1+ EMIT ;

: .blinky  ( -- ) 0  .dwchar ; \ Blinky (instanciated)
: .cross   ( -- ) 2  .dwchar ; \ Erasable/pacman
: .pmrgt   ( -- ) 4  .dwchar ; \ Pacman -> right (instanciated)
: .pmgo    ( -- ) 6  .dwchar ; \ Pacman gobbling
: .llc     ( -- ) 8  .dwchar ;
: .lrc     ( -- ) 10 .dwchar ;
: .hbar    ( -- ) 12 .dwchar ;
: .vbar    ( -- ) 14 .dwchar ;
: .ulc     ( -- ) 16 .dwchar ;
: .urc     ( -- ) 18 .dwchar ;
: .ppl     ( -- ) 20 .dwchar ; \ Erasable/pacman
: .tdn     ( -- ) 22 .dwchar ;
: .tup     ( -- ) 24 .dwchar ;
: .trg     ( -- ) 26 .dwchar ;
: .tlf     ( -- ) 28 .dwchar ;
: .west    ( -- ) 30 .dwchar ;
: .east    ( -- ) 32 .dwchar ;
: .south   ( -- ) 34 .dwchar ;
: .north   ( -- ) 36 .dwchar ;
: .door    ( -- ) 38 .dwchar ; \ Erasable/ghosts in the pen
: .pmlft   ( -- ) 40 .dwchar ; \ Pacman -> left
: .pmupw   ( -- ) 42 .dwchar ; \ Pacman -> up
: .pmdnw   ( -- ) 44 .dwchar ; \ Pacman -> down
: .inky    ( -- ) 46 .dwchar ; \ Inky (instanciated)
: .pinky   ( -- ) 48 .dwchar ; \ Pinky (instanciated)
: .clyde   ( -- ) 50 .dwchar ; \ Clyde (instanciated)
: .rblinky ( -- ) 52 .dwchar ; \ Blinky, reverse video
: .rinky   ( -- ) 54 .dwchar ; \ Inky, reverse video
: .rpinky  ( -- ) 56 .dwchar ; \ Pinky, reverse video
: .rclyde  ( -- ) 58 .dwchar ; \ Clyde, reverse video

\ Select custom character set.
: custom-charset-select ( -- )
  $0E EMIT ;            \ GL <- G1 (LS1 locking shift)

: default-charset-select ( -- )
  $0F EMIT ;            \ GL <- G0 (LS0 locking shift)

\ Used by pacman when entering/leaving the "issuper" state.
IFGF warnings off
: bell ( -- )
  default-charset-select
  7 EMIT
  custom-charset-select ;
IFGF warnings on

: initvars ( -- )
  0 serialno !          \ Entity serial number counter
  0. hiscore 2!         \ Make this somehow persistent!
  0. score  2!
  3. lives  2!          \ This is clearly overkill
  1. gamlev 2!          \ And so is this
  0. bonus  2!          \ Semantics need clarification
  0. suptim 2! ;        \ Semantics need clarification

: initialize ( -- )
  initvars
  IFGF TIME&DATE 2DROP 2DROP DROP \ PRNG initialization
  IFGF ?DUP IF seed ! THEN        \ The seed must be non-zero
  -cursor               \ Cursor off
  -autorepeat           \ Disable keyboard autorepeat
  esc EMIT ."  F"       \ VT400 mode, 7-bit control (PRM/88)
  decdld                \ Upload charset definition
  custom-charset-select ;     \ Select custom character set

: finalize ( -- )
  default-charset-select       \ Select custom character set
  24 79 AT-XY CR
  +autorepeat           \ Re-enable keyboard autorepeat
  +cursor ;             \ Cursor on

: .var ( varaddr -- )
  2@ <# # # # # # # # # #> TYPE ;

: update-score ( -- )
  default-charset-select
  0 4  AT-XY score   .var
  custom-charset-select ;

\ This routine should only be called when the default character
\ set is in effect. Otherwise things will look ugly.
: .sitrep ( -- )
   0 1  AT-XY hiscore .var
   0 4  AT-XY score   .var
   0 7  AT-XY lives   .var
   0 10 AT-XY gamlev  .var
   0 13 AT-XY bonus   .var
   0 16 AT-XY suptim  .var ;

\ Print status headers. Forces in the default character set and
\ leaves in custom character set mode.
: .init-sitrep ( -- )
  default-charset-select
  0 0  AT-XY ." Highscore"
  0 3  AT-XY ." Score"
  0 6  AT-XY ." Lives"
  0 9  AT-XY ." Level"
  0 12 AT-XY ." Bonus"
  0 15 AT-XY ." Supertime"
  .sitrep
  custom-charset-select ;

\ Grid definition language:
\ BL     2 SPACES
\ CHAR A upper left corner
\ CHAR B upper right corner
\ CHAR C Lower left corner
\ CHAR D Lower right corner
\ CHAR E Horizontal bar
\ CHAR F Vertical bar
\ CHAR G T down
\ CHAR H T up
\ CHAR I T left
\ CHAR J T right
\ CHAR K Cross
\ CHAR L Power pellet
\ CHAR M Pacman going right
\ CHAR N Ghost (Blinky)
\ CHAR O West
\ CHAR P East
\ CHAR Q South
\ CHAR S North
\ CHAR T Door
\ CHAR U Pacman going left
\ CHAR V Pacman going upward
\ CHAR W Pacman going downward
\ CHAR X Ghost (Inky)
\ CHAR Y Ghost (Pinky)
\ CHAR Z Ghost (Clyde)
\ CHAR [ Ghost (Blinky) in reverse video
\ CHAR \ Ghost (Inky) in reverse video
\ CHAR ] Ghost (Pinky) in reverse video
\ CHAR ^ Ghost (Clyde) in reverse video -- see also .grid-char

80 #col 2 * - CONSTANT x0

\ Drain the data stack
: drain ( ... -- )
\ ." Data stack depth was " DEPTH .
  BEGIN DEPTH WHILE DROP REPEAT ;

: crash-and-burn ( exitmsg-addr exitmsg-bcnt )
  default-charset-select
  0 23 AT-XY TYPE
  CR .S
  drain +cursor QUIT ;

\ Display grid character (double width) at the current
\ cursor position.
: .grid-char ( grid-char -- )
  DUP BL = IF DROP 2 SPACES EXIT THEN
  DUP [CHAR] A [CHAR] ^ 1+ WITHIN 0= IF
    S" .grid-char: illegal character" crash-and-burn
  THEN

  case!
  BL       case? IF 2 SPACES EXIT THEN
  [CHAR] A case? IF .ulc     EXIT THEN
  [CHAR] B case? IF .urc     EXIT THEN
  [CHAR] C case? IF .llc     EXIT THEN
  [CHAR] D case? IF .lrc     EXIT THEN
  [CHAR] E case? IF .hbar    EXIT THEN
  [CHAR] F case? IF .vbar    EXIT THEN
  [CHAR] G case? IF .tdn     EXIT THEN
  [CHAR] H case? IF .tup     EXIT THEN
  [CHAR] I case? IF .tlf     EXIT THEN
  [CHAR] J case? IF .trg     EXIT THEN
  [CHAR] K case? IF .cross   EXIT THEN
  [CHAR] L case? IF .ppl     EXIT THEN
  [CHAR] M case? IF .pmrgt   EXIT THEN
  [CHAR] N case? IF .blinky  EXIT THEN
  [CHAR] O case? IF .west    EXIT THEN
  [CHAR] P case? IF .east    EXIT THEN
  [CHAR] Q case? IF .south   EXIT THEN
  [CHAR] S case? IF .north   EXIT THEN
  [CHAR] T case? IF .door    EXIT THEN
  [CHAR] U case? IF .pmlft   EXIT THEN
  [CHAR] V case? IF .pmupw   EXIT THEN
  [CHAR] W case? IF .pmdnw   EXIT THEN
  [CHAR] X case? IF .inky    EXIT THEN
  [CHAR] Y case? IF .pinky   EXIT THEN
  [CHAR] Z case? IF .clyde   EXIT THEN
  [CHAR] [ case? IF .rblinky EXIT THEN \ Blinky, reverse video
  [CHAR] \ case? IF .rinky   EXIT THEN \ Inky, reverse video
  [CHAR] ] case? IF .rpinky  EXIT THEN \ Pinky, reverse video
  .rclyde ;                            \ Clyde, reverse video

\ ANS94 3.2.3.3 Return stack:
\ A program shall not access from within a DO-LOOP values
\ placed on the return stack before the loop was entered.
\ Note: this is enforced in SwiftForth but not in Gforth.
: display-line ( caddr len y0 -- )
  OVER #col <> IF
    S" display-line: incorrect column count" crash-and-burn
  THEN

  DUP y0 !         \ caddr\len\y0  backup y0 to a global var.
  x0 SWAP AT-XY    \ caddr\len
  0 DO             \ caddr
    DUP C@ DUP     \ caddr\grid-char\grid-char
    y0 @ #col * I + grid + C!          \ Grid initialization
    .grid-char     \ caddr
    1+
  LOOP DROP ;

\ Display the initial grid contents.
\ Note: this assumes custom-charset-select is in effect.
\ By design no instanciated object should be referenced here.
: .initial-grid ( -- )
  \ 33 columns (double width characters) by 23 rows.
  S" AEEEEEEEGEEEEEEEEEEEEEEEGEEEEEEEB" 0  display-line
  S" FL K K KFK K K K K K K KFK K K LF" 1  display-line
  S" F AEEEP Q OEEEEEEEEEEEP Q OEEEB F" 2  display-line
  S" FKFK K K K K K K K K K K K K KFKF" 3  display-line
  S" F Q S S OEP OEEEEEEEP OEP S S Q F" 4  display-line
  S" FK KFKFK K K K K K K K K KFKFK KF" 5  display-line
  S" JEP F Q OEEEB OEEEP AEEEP Q F OEI" 6  display-line
  S" FK KFK K K KFK K K KFK K K KFK KF" 7  display-line
  S" F S Q OEEEB F ATTTB F AEEEP Q S F" 8  display-line
  S" FKFK K K KFKFKF   FKFKFK K K KFKF" 9  display-line
  S" F F OEEEP F F F   F F F OEEEP F F" 10 display-line
  S" FKFK K K KFKFKF   FKFKFK K K KFKF" 11 display-line
  S" F CEP S S Q Q CEEED Q Q S S OED F" 12 display-line
  S" FK K KFKFK K K K K K K KFKFK K KF" 13 display-line
  S" F OEEED Q S OEEEEEEEP S Q CEEEP F" 14 display-line
  S" FK K K K KFK K K K K KFK K K K KF" 15 display-line
  S" F OEGEEEP Q OEEEEEEEP Q OEEEGEP F" 16 display-line
  S" FK KFK K K K K K K K K K K KFK KF" 17 display-line
  S" JEP F OEP S OEEEEEEEP S OEP F OEI" 18 display-line
  S" FK KFK K KFK K K K K KFK K KFK KF" 19 display-line
  S" F OEHEEEP F OEEEEEEEP F OEEEHEP F" 20 display-line
  S" FL K K K KFK K K K K KFK K K K LF" 21 display-line
  S" CEEEEEEEEEHEEEEEEEEEEEHEEEEEEEEED" 22 display-line ;

\ -------------------------------------------------------------
\ Animation objects.
\ Using a Forth2012 data structure specification sub-set.

IFGF warnings off
\ Under GForth 0.7.3, override the structure related material.
: BEGIN-STRUCTURE  \ -- addr 0 ; -- size
  CREATE
    HERE 0 0 ,     \ mark stack, lay dummy
  DOES>
    @ ;            \ -- rec-len

: +FIELD           \ n <"name"> -- ; Exec: addr -- 'addr
  CREATE
    OVER , +
  DOES>
    @ + ;

: FIELD: ( n1 "name" -- n2 ; addr1 -- addr2 )
  ALIGNED 1 CELLS +FIELD ;

: CFIELD: ( n1 "name" -- n2 ; addr1 -- addr2 )
  1 CHARS +FIELD ;

: END-STRUCTURE    \ addr n --
   SWAP ! ;        \ set len
IFGF warnings on

BEGIN-STRUCTURE entity
  FIELD:  e.strategy \ Strategy (moving) method
  FIELD:  e.display  \ Display method
  FIELD:  e.resurr   \ # Clock ticks till we're back (ghosts)
  CFIELD: e.vrow#    \ Virtual row number
  CFIELD: e.pcol#    \ Physical column number
  CFIELD: e.ivrow#   \ Interfering virtual row number (ghosts)
  CFIELD: e.ipcol#   \ Interfering pcol number (ghosts)
  CFIELD: e.igchr    \ Interfering grid character (ghosts)
  CFIELD: e.pcol0    \ Initial pcol number
  CFIELD: e.vrow0    \ Initial vrow number
  CFIELD: e.cdir     \ Current direction
  CFIELD: e.pdir     \ Previous direction (pacman)
  CFIELD: e.idir     \ Intended direction (pacman)
  CFIELD: e.inited   \ TRUE if first display has been performed
  CFIELD: e.issuper  \ # Clock ticks in "super" state (pacman)
  CFIELD: e.isalive  \ NZ if ghost and not neutralized
  CFIELD: e.gobbling \ # Clock ticks till we're fed (pacman)
  CFIELD: e.inum     \ Instance serial number
END-STRUCTURE

\ Method invokator.
: :: ( method-xt-addr -- ) @ EXECUTE ;

\ We define this enumeration so that opposite(dir) is
\ dir 2 + 3 AND (modulo 4) for dir in [0..3].
0 CONSTANT dir_up
1 CONSTANT dir_left
2 CONSTANT dir_down
3 CONSTANT dir_right
4 CONSTANT dir_blocked
5 CONSTANT dir_unspec \ Invalid except for idir (pacman)
6 CONSTANT dir_quit \ Invalid except as retval/pacman.dirselect

\ Display pacman--rendition depends on the current direction
\ and gobbling status. Gobbling overrides the direction
\ indication.
: .pacman ( self -- )
  DUP e.gobbling C@ ?DUP IF \ self\gobbling-cycle-count
    .pmgo          \ Display pacman as gobbling
    1- SWAP e.gobbling C!
    EXIT
  THEN

  DUP e.cdir C@ DUP dir_blocked = IF
    DROP
    e.pdir C@
  ELSE
    NIP
  THEN

  case!
  dir_right case? IF .pmrgt EXIT THEN
  dir_left  case? IF .pmlft EXIT THEN
  dir_up    case? IF .pmupw EXIT THEN
  dir_down  case? IF .pmdnw EXIT THEN ;

\ Display entity.
: entity.display ( self -- )
  DUP e.inum C@ case!
  0 case? IF
    .pacman ( self is consumed ) EXIT
  ELSE
    DROP           \ No further introspection is required
  THEN

  pacman-addr e.issuper C@ 0= IF \ Ghosts are not frightened
    1 case? IF .blinky  EXIT THEN
    2 case? IF .inky    EXIT THEN
    3 case? IF .pinky   EXIT THEN
    4 case? IF .clyde   EXIT THEN
  ELSE                           \ They are. Use reverse video
    1 case? IF .rblinky EXIT THEN
    2 case? IF .rinky   EXIT THEN
    3 case? IF .rpinky  EXIT THEN
    4 case? IF .rclyde  EXIT THEN
  THEN

  S" entity.display: unknown instance number" crash-and-burn ;

: bitclear ( val bitno -- val-new )
  1 SWAP LSHIFT INVERT AND ;

: bitset? ( val bitno -- flag )
  1 SWAP LSHIFT AND ( 0<> ) ;

: >grid-space ( vrow#|pcol# -- grid-index ) 1 RSHIFT ;

\ If moving horizontally, the resulting pcol must be
\ >= 2 and < 64.
: valid-pcol? ( col -- col flag ) DUP 2 64 WITHIN ;

\ If moving vertically, the resulting vrow number must be
\ >= 2 and < 44.
: valid-vrow? ( row -- row flag ) DUP 2 44 WITHIN ;

: scorable? ( uchar -- flag )
  DUP cross = SWAP pellet = OR ;

: erasable? ( uchar -- flag )
  DUP BL = IF DROP TRUE EXIT THEN
  scorable? ;

: erasable-or-door? ( uchar -- flag )
  DUP door = IF DROP TRUE EXIT THEN
  erasable? ;

: in-ghosts-pen? ( self -- flag )
  DUP  e.vrow# C@ 16 23 WITHIN
  SWAP e.pcol# C@ 30 35 WITHIN AND ;

: get-grid-char-addr ( pcol vrow -- grid-char-addr )
  \ pcol and vrow are supposed to have been previously
  \ validated.
  >grid-space #col * SWAP >grid-space + grid + ;

\ Returns the grid character at [vrow, pcol].
: get-grid-char ( pcol vrow -- grid-char )
  \ Enforce assumptions.
  valid-vrow? 0= IF
    S" vrow# is out of bounds" crash-and-burn
  THEN
  OVER valid-pcol? NIP 0= IF
    S" pcol# is out of bounds" crash-and-burn
  THEN

  get-grid-char-addr C@ ;

\ Note: ghost.dirselect guarantees us that both pcol# and
\ vrow# are even.
: can-move-in-dir? ( self dir -- flag )
  case!            \ S: self
  >R               \ S: -- ; R: self
  dir_left  case? IF
    R@ e.pcol# C@ 2 - valid-pcol? R@ e.vrow# C@ SWAP
  THEN
  dir_right case? IF
    R@ e.pcol# C@ 2 + valid-pcol? R@ e.vrow# C@ SWAP
  THEN
  dir_up    case? IF
    R@ e.pcol# C@ R@ e.vrow# C@ 2 - valid-vrow?
  THEN
  dir_down  case? IF
    R@ e.pcol# C@ R@ e.vrow# C@ 2 + valid-vrow?
  THEN

  \ pcol-new\vrow-new\validf
  IF               \ Still need to check for walls!!!
    get-grid-char DUP erasable? IF
      DROP TRUE
    ELSE
      \ The grid character might not be considered as an
      \ erasable and still may be if:
      \ 1: the grid character is 'T' (ghosts' pen door).
      \ 2: we're a ghost (i.e. not pacman).
      \ 3: the originating coordinates are inside the ghosts'
      \    pen.
      \ In essence, the ghosts' pen door _is_ an erasable but
      \ only for the ghosts when they are inside of the pen.
      door =   \ Ghosts' pen door
      R@ e.inum C@ 0<> AND \ We are not pacman
      R@ in-ghosts-pen? AND      
    THEN
  ELSE
    2DROP FALSE
  THEN
  R> DROP ;

\ Debugging support.
: debug-enter ( -- )
  debug 0= IF EXIT THEN
  default-charset-select
  0 23 AT-XY 78 SPACES
  0 23 AT-XY ;

: debug-leave ( -- )
  debug 0= IF EXIT THEN
  custom-charset-select
  KEY DROP ;

: ghost.debug-print ( pcol-new vrow-new debug-tag-char self --
    pcol-new vrow-new )
  DUP e.inum C@ 0= IF 2DROP EXIT THEN \ If not a ghost
  debug 1 AND 0=   IF 2DROP EXIT THEN \ If not in debug mode
  debug-enter
  >R
  EMIT [CHAR] : EMIT SPACE
  ." Cdir: " R@ e.cdir C@ .

  ." Cpos: "
  [CHAR] [ EMIT
  R@ e.vrow# C@ 0 .R SPACE \ vrow-cur
  R@ e.pcol# C@ 0 .R       \ pcol-cur
  [CHAR] ] EMIT SPACE

  ." Npos: "
  [CHAR] [ EMIT
  2DUP 0 .R SPACE          \ vrow-new
       0 .R                \ pcol-new
  [CHAR] ] EMIT SPACE

  ." Interf: "
  R@ e.igchr C@ ?DUP IF ELSE [CHAR] - THEN EMIT SPACE
  [CHAR] [ EMIT
  R@ e.ivrow# C@ 0 .R SPACE
  R@ e.ipcol# C@ 0 .R
  [CHAR] ] EMIT
  R> DROP
  debug-leave ;

\ Meant for interactive (post-mortem) use.
: .dir ( dir -- )
  case!
  dir_up      case? IF ." UP"      EXIT THEN
  dir_left    case? IF ." LEFT"    EXIT THEN
  dir_down    case? IF ." DOWN"    EXIT THEN
  dir_right   case? IF ." RIGHT"   EXIT THEN
  dir_blocked case? IF ." BLOCKED" EXIT THEN
  dir_unspec  case? IF ." UNSPEC"  EXIT THEN
  dir_quit    case? IF ." QUIT"    EXIT THEN
  ." Unknown quantity: " case@ . ;

: keyboard-input-query ( -- dir_symbol )
  KEY? 0= IF dir_unspec EXIT THEN

  KEY DUP [CHAR] q = IF DROP dir_quit EXIT THEN
  esc <>             IF dir_unspec    EXIT THEN
  KEY [CHAR] [ <>    IF dir_unspec    EXIT THEN
  KEY case!
  [CHAR] A case?     IF dir_up        EXIT THEN
  [CHAR] B case?     IF dir_down      EXIT THEN
  [CHAR] C case?     IF dir_right     EXIT THEN
  [CHAR] D case?     IF dir_left      EXIT THEN

  S" keyboard-input-query: no comprendo"
    crash-and-burn ;

: pacman.dirselect ( self -- new-dir )
  \ Keyboard input overrides any previous intended direction.
  keyboard-input-query case!
  dir_unspec case? 0= IF \ There was some input
    dir_quit  case? IF S" Exiting game" crash-and-burn THEN
    \ If a direction change is requested via keyboard input:
    \ mark it as the intended direction (idir) and proceed.
    dir_up    case?
    dir_down  case? OR
    dir_left  case? OR
    dir_right case? OR IF
      case@ OVER e.idir C!      
    THEN
  THEN

  \ No direction changes unless both vrow# and pcol# are even.
  DUP e.vrow# C@ 1 AND IF e.cdir C@ EXIT THEN
  DUP e.pcol# C@ 1 AND IF e.cdir C@ EXIT THEN

  \ If idir is not dir_unspec AND we can move in idir:
  \ - queue up idir as the return value.
  \ - reset idir to dir_unspec.
  \ - end of story.
  >R
  R@ e.idir C@ dir_unspec <> IF
    R@ DUP e.idir C@ can-move-in-dir? IF
      R@ e.idir C@ \ Queue up return value
      dir_unspec R@ e.idir C!
      R> DROP EXIT
    THEN
  THEN

  \ Default policy: keep the current direction unless blocked.
  R@ e.cdir C@ dir_blocked = IF
    R> DROP dir_blocked EXIT
  THEN

  R@ DUP e.cdir C@ can-move-in-dir? IF
    R> e.cdir C@ EXIT
  THEN

  R> DUP e.cdir C@ SWAP e.pdir C!
  dir_blocked ;

: ghost.dirselect ( self -- new-dir )
  \ No direction changes unless both vrow# and pcol# are even.
  DUP e.vrow# C@ 1 AND IF e.cdir C@ EXIT THEN
  DUP e.pcol# C@ 1 AND IF e.cdir C@ EXIT THEN

  \ All directions should be considered equally. By policy, we
  \ choose to exclude opposite(cdir), i.e. we're not going
  \ back on our steps. The grid has no dead end so we will end
  \ up with at least one viable option.
  %1111            \ The sum of a priori alternatives
  OVER e.cdir C@
    2 + 3 AND
    bitclear       \ Exclude opposite(cdir)

  debug 2 AND IF
    debug-enter  ." bitmap A: " DUP .  debug-leave
  THEN

  \ S: self\bitmap
  dir_right 1+ dir_up DO
    DUP I bitset? IF \ Direction I is a priori viable
      OVER I can-move-in-dir? \ Check for a possible obstacle
      0= IF        \ Blocked in direction I
        I bitclear
      THEN
    THEN
  LOOP

  debug 2 AND IF
    debug-enter  ." bitmap B: " DUP .  debug-leave
  THEN

  \ If we are inside of the ghosts' pen and the current
  \ direction remains an option, stick to it.
  OVER in-ghosts-pen? IF \ S: self\bitmap
    OVER e.cdir C@ \ S: self\bitmap\cdir
    1 SWAP LSHIFT  \ S: self\bitmap\1<<cdir
    OVER AND IF    \ S: self\bitmap
      DROP e.cdir C@ EXIT
    THEN
  THEN

  NIP              \ S: bitmap
  dir_right 1+ dir_up DO
    DUP 1 AND      \ S: bitmap\bit0(bitmap)
    SWAP 1 RSHIFT SWAP  \ S: bitmap>>1\bit0(bitmap)
    IF             \ bit0(bitmap) is set; S: bitmap>>1
      ?DUP IF      \ There are other possible directions
        random 8 AND IF
          DROP I UNLOOP EXIT \ Select direction I
        THEN
      ELSE         \ There are no alternatives left
        I UNLOOP EXIT
      THEN
    THEN
  LOOP

  S" ghost.dirselect: no viable direction found"
    crash-and-burn ;

\ Re-display an erasable that was at least partially
\ obscured by a ghost passing by.
: .interfering ( self -- )
  >R
  R@ e.igchr C@ IF
    R@ e.ipcol# C@ x0 + R@ e.ivrow# C@ >grid-space AT-XY
      R@ e.igchr C@ .grid-char
  THEN
  R> DROP ;

\ Utility routine--not a method.
: entity.initial-display ( self -- )
  >R
  R@ e.pcol# C@ x0 +
    R@ e.vrow# C@ >grid-space
    AT-XY  R@ DUP e.display ::
  R> DROP ;

\ Utility routine--not a method.
: entity.get-new-coordinates ( self -- pcol-new\vrow-new )
  >R
  R@ e.cdir C@ case!
  dir_left    case? IF R@ e.pcol# C@ 1- R@ e.vrow# C@    THEN
  dir_right   case? IF R@ e.pcol# C@ 1+ R@ e.vrow# C@    THEN
  dir_up      case? IF R@ e.pcol# C@    R@ e.vrow# C@ 1- THEN
  dir_down    case? IF R@ e.pcol# C@    R@ e.vrow# C@ 1+ THEN

  \ The following applies only to pacman (not enforced).
  dir_blocked case? IF R@ e.pcol# C@    R@ e.vrow# C@    THEN
  R> DROP ;

\ Utility routine--not a method.
\ Do not preserve erasables.
\ Manage gobbling aspect. This requires an update to 'grid'.
\ Update the score accordingly.
: pacman.moving-policy ( pcol-new vrow-new self --
    pcol-new vrow-new )
  >R
  OVER 1 AND 0=        \ pcol-new is even
  OVER 1 AND 0= AND IF \ and so is vrow-new
    2DUP get-grid-char DUP
    scorable? IF       \ Cross or pellet
      2 R@ e.gobbling C!  \ Gobble for two clock cycles

      case! score DUP 2@
      cross  case? IF 10. THEN
      pellet case? IF  \ Enter "supercharged" mode
        super-clkcycles R@ e.issuper C! \ A clock cycle count
        bell 50.
      THEN
      D+ ROT 2!
      update-score

      \ Cross or pellet consumed. Blank the grid character.
      2DUP get-grid-char-addr BL SWAP C!

    ELSE
      DROP
    THEN
  THEN

  \ Decrement the e.issuper attribute if non zero.
  R@ e.issuper C@ ?DUP IF
    1- R@ e.issuper C!
    R@ e.issuper C@ 0= IF bell THEN \ Leave "supercharged" mode
  THEN

  R> DROP ;

\ Utility routine--not a method.
\ Preserve erasables.
\ Eventually check whether we caught pacman and he must die.
: ghost.moving-policy ( pcol-new vrow-new self --
    pcol-new vrow-new )
  >R
  \ Check whether we previously saved an interfering character.
  \ If so, re-display it at the saved coordinates.
  R@ .interfering

  [CHAR] C R@ ghost.debug-print

  \ Defer the "save-under" logic until pcol-new is even.
  \ pcol-new\vrow-new
  OVER 1 AND IF R> DROP EXIT THEN

  [CHAR] D R@ ghost.debug-print

  \ Are we stepping on anyone's toes (interfering)?
  \ Note: interference is checked at the new coordinates.
  2DUP get-grid-char

  \ A non-BL erasable character is said to be interfering.
  DUP DUP BL <> SWAP erasable-or-door? AND IF
    \ Did we already know about it?
    R@ e.igchr C@ IF \ Yes

      \ Check for a new interference.
      DUP R@ e.igchr C@ <> IF \ Interfering differently
        R@ .interfering
        R@ e.igchr C!
        \ Update interference details.
        2DUP  -2 AND R@ e.ivrow# C! \ Force even row#
          R@ e.ipcol# C!
      ELSE           \ Same old
        DROP         \ Drop interfering character
      THEN

    ELSE             \ No, register interference details
      R@ e.igchr C!
      2DUP  -2 AND R@ e.ivrow# C! \ Force even row#
        R@ e.ipcol# C!
      [CHAR] E R@ ghost.debug-print
    THEN
  ELSE
    DROP             \ Drop interfering character
    R@ .interfering
    0 R@ e.igchr C!  \ Clear interference record
  THEN
  R> DROP ;

\ Entity method.
: entity.move ( self -- )
  >R

  R@ e.inited C@ 0= IF \ If this is the first display request.
    R@ entity.initial-display
    TRUE R> e.inited C! EXIT
  THEN

  \ The current direction should be in [dir_up..dir_blocked]
  \ Bail out now if that's not the case.
  \ dir_blocked should only be in effect for pacman, which
  \ is an indication that some keyboard input is required.
  R@ e.cdir C@ dir_up dir_blocked 1+ WITHIN 0= IF
    S" entity.move: illegal current direction" crash-and-burn
  THEN
  \ From here on, cdir has been validated.

  R@ DUP DUP e.inum C@ IF
    ghost.dirselect
  ELSE
    pacman.dirselect
  THEN
  SWAP e.cdir C!

  \ The current entity has been displayed at least once and
  \ cdir is viable. We are now in a position such that we can
  \ actually alter the entity's coordinates.

  -1 -1 [CHAR] A R@ ghost.debug-print 2DROP

  \ Blank current position on screen.
  R@ e.pcol# C@ x0 + R@ e.vrow# C@ >grid-space AT-XY 2 SPACES

  \ Update entity coordinates on the data stack.
  R@ entity.get-new-coordinates \ pcol-new\vrow-new

  [CHAR] B R@ ghost.debug-print

  R@ DUP e.inum C@ IF \ pcol-new\vrow-new\self
    ghost.moving-policy
  ELSE
    pacman.moving-policy
  THEN

  [CHAR] F R@ ghost.debug-print

  \ Update entity's coordinates fields.
  2DUP  R@ e.vrow# C!  R@ e.pcol# C!

  \ Display entity at new coordinates.
  SWAP x0 + SWAP >grid-space AT-XY R@ DUP e.display ::

  -1 -1 [CHAR] G R@ ghost.debug-print 2DROP

  R> DROP ;

\ Entity constructor.
: entity.new ( "name" -- address ; vrow pcol cdir -- )
  CREATE
    entity ALLOT
  DOES>            \ vrow\pcol\cdir\address
    >R             \ vrow\pcol\cdir, R: address
    \ Initialize default valued fields.
    ['] entity.move    R@ e.strategy !
    ['] entity.display R@ e.display  !
    0                  R@ e.resurr   !
    0                  R@ e.ivrow#   C!
    0                  R@ e.ipcol#   C!
    0                  R@ e.igchr    C!
    dir_blocked        R@ e.pdir     C!
    dir_unspec         R@ e.idir     C!
    FALSE              R@ e.inited   C!
    FALSE              R@ e.issuper  C!
    TRUE               R@ e.isalive  C!
    0                  R@ e.gobbling C!
    serialno @ DUP     R@ e.inum     C!
      1+ serialno !
    \ Initialize fields from arguments.
    R@ e.cdir  C!                   \ vrow\pcol
    DUP R@ e.pcol0 C! R@ e.pcol# C! \ vrow
    DUP R@ e.vrow0 C! R@ e.vrow# C! \ --
    R> ;           \ Return 'address'

4 CONSTANT #ghosts
#ghosts 1+ CONSTANT #entities
CREATE entvec #entities CELLS ALLOT

entvec
  \ By convention, we have pacman as instance #0.
  entity.new pacman
  34 32 dir_right pacman
  OVER ! CELL+

  entity.new blinky
  14 32 dir_left blinky \ North central ghost
  OVER ! CELL+

  entity.new inky
  20 30 dir_down inky   \ Western ghost
  OVER ! CELL+

  entity.new pinky
  20 32 dir_up pinky    \ Central ghost
  OVER ! CELL+

  entity.new clyde
  20 34 dir_left clyde  \ Eastern ghost
  OVER ! CELL+
DROP                    \ Last defined entity

\ -------------------------------------------------------------
\ Entry point here.

: _main ( -- )
  BEGIN
    entvec @ DUP e.strategy :: \ Pacman's move
    entvec 1 CELLS + #ghosts 0 ?DO
      DUP @ DUP e.strategy :: \ Move the current ghost
      CELL+
    LOOP DROP
    clkperiod MS
  AGAIN ;

: main ( -- )
  initialize
  entvec @ TO pacman-addr
  PAGE .init-sitrep \ Initial scoreboard
  .initial-grid

  IFZ7 _main finalize
  IFGF ['] _main CATCH finalize
  IFGF ?DUP IF
  IFGF   0 23 AT-XY ." Caught exception " DUP . CR
  IFGF   THROW      \ We still want a stack dump!
  IFGF THEN
;

main

\ wasteit

