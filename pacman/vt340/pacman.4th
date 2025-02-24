\ Disclaimer: this code is VT340 specific!
\
\ See https://github.com/hackerb9/vt340test/tree/main/docs
\ for the programmer's reference manual (PRM).
\
\ The code was developed under Gforth 0.7.3.
\
\ The magic incantation to start getty (as root) is:
\
\ /bin/stty -F /dev/ttyS0 19200
\ exec < /dev/ttyS0
\ exec /usr/bin/setsid -c \
\    /sbin/agetty -8 -c -s -L ttyS0 19200 vt340
\
\ You might elect to mess up with systemd's configuration.
\ I do not.
\
\ Game reference material:
\ - the "pacman dossier:"
\   https://pacman.holenet.info/
\ - "GameInternals:"
\   https://gameinternals.com/
\     understanding-pac-man-ghost-behavior

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

IFZ7 : D>S DROP ;
IFZ7 : ?EXIT POSTPONE IF POSTPONE EXIT POSTPONE THEN ;
IFZ7   IMMEDIATE

\ A poor man's replacement for the ANS94 CASE construct.
VARIABLE _case

: case! _case ! ;
: case@ _case @ ;
: case? case@ = ;

\ -------------------------------------------------------------
\ Debugging support constants.

\ bit #0: enable traces in entity.move
\ bit #1: enable traces in ghost.dirselect 
%00 CONSTANT debug

\ -------------------------------------------------------------
\ Pseudo-random number generator.
\ Using John Metcalf's Xorshift LFSRs PRNG.
\ http://www.retroprogramming.com/2017/07/
\   xorshift-pseudorandom-numbers-in-z80.html
VARIABLE seed

: random ( -- N )
  seed @ DUP 7 LSHIFT XOR
  DUP 9 RSHIFT XOR
  DUP 8 LSHIFT XOR
  DUP seed ! ;

\ -------------------------------------------------------------
\ Games counter variables implemented as doubles so as to be
\ able to support 16 bit cell targets.
IFZ7 : 2VARIABLE VARIABLE 1 CELLS ALLOT ;

\ D= is ANS94 Double. That's beyond Core.
IFZ7 : D= D- D0= ;

2VARIABLE hiscore
2VARIABLE score
2VARIABLE lives   \ This is clearly overkill
2VARIABLE gamlev  \ And so is this
2VARIABLE bonus   \ Semantics need clarification
2VARIABLE suptim  \ Semantics need clarification
0 VALUE pacman-addr \ An alias for entvec[0]
VARIABLE y0       \ Used by 'display-line' for inits purposes
VARIABLE serialno \ Instance number generator.

VARIABLE remitems# 0 remitems# !

\ Disable BELL if TRUE
FALSE CONSTANT silent

\ A clock cycle count during which PM stays "supercharged."
120 1+ CONSTANT super-clkcycles

\ 9600 bps: interactivity is lost if we go below 130 MS
IFGF 170 CONSTANT clkperiod \ Expressed in milliseconds
IFZ7 120 CONSTANT clkperiod \ Expressed in milliseconds

\ The entity vector.
4 CONSTANT #ghosts
#ghosts 1+ CONSTANT #entities
CREATE entvec #entities CELLS ALLOT

\ Forward references...
DEFER fright_timer
DEFER super-enter
DEFER super-leave

\ This does not belong here and yet VALUE references cannot
\ be DEFERred in a universally portable way. So it goes...
0 CONSTANT mode_scatter
1 CONSTANT mode_chase \ Each ghost may defines its own policy!
2 CONSTANT mode_fright
3 CONSTANT mode_unspec

\ Those are global variables (in disguise).
mode_scatter VALUE gm_cur \ Current mode
mode_unspec  VALUE gm_prv \ Previous mode

TRUE VALUE gm_timer_en

\ -------------------------------------------------------------
\ Grid specification.

33 CONSTANT #col
23 CONSTANT #row
#col #row * CONSTANT gridsize
CREATE grid gridsize ALLOT
172 CONSTANT #items

\ -------------------------------------------------------------
\ Well known symbols.

CHAR T CONSTANT door
CHAR K CONSTANT cross
CHAR L CONSTANT pellet

\ -------------------------------------------------------------
\ Cursor control. VT200 control sequences.

$1B CONSTANT esc

\ Turn off the cursor.
: -cursor ( -- ) esc EMIT ." [?25l" ;

\ Turn on the cursor.
: +cursor ( -- ) esc EMIT ." [?25h" ;

\ -------------------------------------------------------------
\ Select Graphic Rendition (SGR). VT100 control sequences.

\ Control Sequence Introducer.
: csi ( -- ) esc EMIT [CHAR] [ EMIT ;

\ Select 'bold' character rendition.
: bold-sgr ( -- ) csi ." 1m" ;

\ Select 'All attributes off' character rendition.
: default-sgr csi ." 0m" ;

\ -------------------------------------------------------------
\ Drain terminal output (DECXCPR).

: tty-drain ( -- )
  csi ." 5n"
  KEY KEY 2DROP   \ Skip CSI in the reply
  KEY KEY 2DROP ; \ 0n is OK, 3n indicates a malfunction

\ -------------------------------------------------------------
\ Device Status Report/Cursor Position Report (DSR/CPR).
\ VT100 control sequences.

\ : get-xy ( -- x y )
\   csi ." 6n"
\ 
\   \ Expected reply is: csi <line#> ; <col#> R
\   \ Caution: line#/col# are numbered starting from 1!
\   \ This is a fast and loose implementation in the sense that
\   \ we do not even make sure that the first two characters
\   \ of the reply are esc [ (CSI).
\   pad BEGIN
\     KEY 2DUP
\     SWAP C!
\     SWAP 1+ SWAP
\     [CHAR] R =
\   UNTIL
\   pad -            \ TOS has the reply length in bytes
\ 
\   2 - >R           \ Skip CSI in the reply
\   0. pad 2 + R> >NUMBER
\   1- SWAP 1+ SWAP
\   0. 3 ROLL 3 ROLL >NUMBER
\   2DROP D>S 1-
\   -ROT D>S 1- ;

\ -------------------------------------------------------------
\ VT340 specific material (user defined font definition).

\ Screen resolution is 800x480 in 80 column mode.
\ Characters are defined by a 10 (width) by 20 (height) matrix.
1  CONSTANT pfn
1  CONSTANT pcn   \ First soft char at $21--do not override BL!
1  CONSTANT pe    \ Erase only new definitions
10 CONSTANT pcmw  \ Character width is 10 pixels in 80 col mode
0  CONSTANT pss   \ 80 columns, 24 lines
2  CONSTANT pt    \ Full cell
20 CONSTANT pcmh  \ Character height is 16: 6/6/6/2 in sixels
0  CONSTANT pcss  \ 94-charset, $20 (BL) and $7E (~) are RO
85 CONSTANT ufn   \ User font name is 'U' (argument to DSCS)

pcmh 5 + 6 / CONSTANT nsixels    \ Sixels per column
nsixels pcmw * CONSTANT chrdefbcnt \ Per-char def. byte count

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
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #2
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #6
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #7
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #9

\ Character "blinky", right half at $22 (").
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #2
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "cross", left half at $23 (#).
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #3
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #4
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #5
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #6
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #7
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #8
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #9

\ Character "cross", right half at $24 ($).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #0
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #2
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #3
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #4
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #5
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Pacman going right", left half at $25 (%).
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #6
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #7
%001100 C, %000011 C, %111111 C, %000000 C, \ Column #8
%001100 C, %000011 C, %111111 C, %000000 C, \ Column #9

\ Character "Pacman going right", right half at $26 (&)
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %000000 C, %111100 C, %000000 C, \ Column #0
%111100 C, %000000 C, %111100 C, %000000 C, \ Column #1
%001100 C, %000000 C, %111100 C, %000000 C, \ Column #2
%001100 C, %000000 C, %111100 C, %000000 C, \ Column #3
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #4
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Pacman (gobbling)", left half at $27 (').
\ Left: colunm #0 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #4
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #5
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #6
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #7
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #8
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #9

\ Character "Pacman (gobbling)", right half at $28 (()
\ Right: column #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #0
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #2
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #3
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #4
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111100 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Lower left corner", left half at $29 ()).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%111111 C, %011111 C, %000000 C, %000000 C, \ Column #4
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #5
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #6
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #7
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #8
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Lower left corner", right half at $2A (*).
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #0
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #1
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #2
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #3
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #4
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Lower right corner", left half at $2B (+).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #4
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #5
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #6
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #7
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #8
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Lower right corner", right half at $2C (,).
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #0
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #1
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #2
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #3
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #4
%111111 C, %011111 C, %000000 C, %000000 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Horizontal bar", left half at $2D (-).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #4
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Horizontal bar", right half at $2E (.).
\ Group A  Group B    Group C (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #4
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Vertical bar", left half at $2F (/).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #4
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #5
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #6
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #7
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #8
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "Vertical bar", right half at $30 (0).
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #0
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #1
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #2
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #3
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #4
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Upper left corner", left half at $31 (1).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%000000 C, %111000 C, %111111 C, %000011 C, \ Column #4
%000000 C, %111110 C, %111111 C, %000011 C, \ Column #5
%000000 C, %111110 C, %111111 C, %000011 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #7
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #8
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "Upper left corner", right half at $32 (2).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #0
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #2
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #3
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #4
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Upper right corner", left half at $33 (3).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #4
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #7
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #8
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "Upper right corner", right half at $34 (4).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #0
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #2
%000000 C, %111110 C, %111111 C, %000011 C, \ Column #3
%000000 C, %111110 C, %111111 C, %000011 C, \ Column #4
%000000 C, %111000 C, %111111 C, %000011 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Power pellet", left half at $35 (5).
\ Left: colunm #0 and unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #2
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #6
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #7
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #8
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #9

\ Character "Power pellet", right half at $36 (6).
\ Right: column #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #0
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #2
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #6
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "T down", left half at $37 (7).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000111 C, %000000 C, \ Column #2
%000000 C, %111111 C, %001111 C, %000000 C, \ Column #3
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #4
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #7
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #8
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "T down", right half at $38 (8).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #0
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #2
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #3
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #4
%000000 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %111111 C, %001111 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000111 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "T up", left half at $39 (9).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%100000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%110000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #4
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #5
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #6
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #7
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #8
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "T up", right half at $3A (:).
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #0
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #1
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #2
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #3
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #4
%111111 C, %111111 C, %000011 C, %000000 C, \ Column #5
%110000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%100000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "T right", left half at $3B (;).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #4
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #5
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #6
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #7
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #8
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "T right", right half at $3C (<).
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #0
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #1
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #2
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #3
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #4
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #5
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #6
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "T left", left half at $3D (=).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%100000 C, %111111 C, %000111 C, %000000 C, \ Column #2
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #3
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #4
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #5
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #6
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #7
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #8
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "T left", right half at $3E (>).
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #0
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #1
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #2
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #3
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #4
%111111 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "West", left half at $3F (?).
\ Columns #0 and #1 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %011000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #3
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #4
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "West", right half at $40 (@).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #4
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "East", left half at $41 (A).
\ Columns #0 and #1 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #4
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "East", right half at $42 (B).
\ Columns #8 and #9 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #2
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #3
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #4
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #5
%000000 C, %111110 C, %000001 C, %000000 C, \ Column #6
%000000 C, %011000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "South", left half at $43 (C).
\ Columns #0 through #3 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%111111 C, %011111 C, %000000 C, %000000 C, \ Column #4
%111111 C, %111111 C, %000000 C, %000000 C, \ Column #5
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #6
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #7
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #8
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #9

\ Character "South", right half at $44 (D).
\ Columns #6 and #9 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #0
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #1
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #2
%111111 C, %111111 C, %000001 C, %000000 C, \ Column #3
%111111 C, %111111 C, %000000 C, %000000 C, \ Column #4
%111111 C, %011111 C, %000000 C, %000000 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "North", left half at $45 (E).
\ Columns #0 through #3 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%100000 C, %111111 C, %111111 C, %000011 C, \ Column #4
%110000 C, %111111 C, %111111 C, %000011 C, \ Column #5
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #6
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #7
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #8
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #9

\ Character "North", right half at $46 (F).
\ Columns #6 and #9 are unsused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #0
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #1
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #2
%111000 C, %111111 C, %111111 C, %000011 C, \ Column #3
%110000 C, %111111 C, %111111 C, %000011 C, \ Column #4
%100000 C, %111111 C, %111111 C, %000011 C, \ Column #5
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #6
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Door", left half at $47 (G).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #0
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #1
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #2
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #3
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #4
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #5
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #6
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #7
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #8
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #9

\ Character "Door", right half at $48 (H).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #0
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #1
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #2
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #3
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #4
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #5
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #6
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #7
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #8
%000000 C, %000011 C, %000011 C, %000000 C, \ Column #9

\ Character "Pacman going left", left half at $49 (I).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #2
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #3
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #4
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #5
%001100 C, %000000 C, %111100 C, %000000 C, \ Column #6
%001100 C, %000000 C, %111100 C, %000000 C, \ Column #7
%111100 C, %000000 C, %111100 C, %000000 C, \ Column #8
%111100 C, %000000 C, %111100 C, %000000 C, \ Column #9

\ Character "Pacman going left", right half at $4A (J).
\ Group A  Group B    Group C    Group D (top to bottom)
%001100 C, %000011 C, %111111 C, %000000 C, \ Column #0
%001100 C, %000011 C, %111111 C, %000000 C, \ Column #1
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #2
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Pacman going up", left half at $4B (K).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%000000 C, %111111 C, %000111 C, %000000 C, \ Column #2
%000000 C, %111111 C, %001111 C, %000000 C, \ Column #3
%000000 C, %110000 C, %001111 C, %000000 C, \ Column #4
%000000 C, %110000 C, %001111 C, %000000 C, \ Column #5
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #6
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #7
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #8
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #9

\ Character "Pacman going up", right half at $4C (L).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #0
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #1
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #2
%000000 C, %000000 C, %011111 C, %000000 C, \ Column #3
%000000 C, %110000 C, %001111 C, %000000 C, \ Column #4
%000000 C, %110000 C, %001111 C, %000000 C, \ Column #5
%000000 C, %001100 C, %001111 C, %000000 C, \ Column #6
%000000 C, %001100 C, %000111 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Pacman going down", left half at $4D (M).
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #0
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #1
%100000 C, %110011 C, %000000 C, %000000 C, \ Column #2
%100000 C, %110011 C, %000000 C, %000000 C, \ Column #3
%110000 C, %001111 C, %000000 C, %000000 C, \ Column #4
%110000 C, %001111 C, %000000 C, %000000 C, \ Column #5
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #6
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #7
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #8
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #9

\ Character "Pacman going down", right half at $4E (N).
\ Group A  Group B    Group C    Group D (top to bottom)
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #0
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #1
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #2
%111000 C, %000011 C, %000000 C, %000000 C, \ Column #3
%110000 C, %001111 C, %000000 C, %000000 C, \ Column #4
%110000 C, %001111 C, %000000 C, %000000 C, \ Column #5
%100000 C, %111111 C, %000011 C, %000000 C, \ Column #6
%100000 C, %111111 C, %000011 C, %000000 C, \ Column #7
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #8
%000000 C, %111111 C, %000011 C, %000000 C, \ Column #9

\ Character "Inky", left half at $4F (O)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #2
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #6
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #7
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %001100 C, %000000 C, \ Column #9

\ Character "Inky", right half at $50 (P).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %001100 C, %000000 C, \ Column #0
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #2
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001111 C, %000000 C, \ Column #5
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Pinky", left half at $51 (Q)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #2
%000000 C, %111111 C, %111011 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001101 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001110 C, %000000 C, \ Column #5
%110000 C, %010011 C, %111111 C, %000000 C, \ Column #6
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #7
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #9

\ Character "Pinky", right half at $52 (R).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #2
%110000 C, %010011 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001110 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001101 C, %000000 C, \ Column #5
%000000 C, %111111 C, %111011 C, %000000 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "Clyde", left half at $53 (S)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #1
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #2
%000000 C, %011111 C, %111111 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001110 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001101 C, %000000 C, \ Column #5
%110000 C, %110011 C, %111011 C, %000000 C, \ Column #6
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #7
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #9

\ Character "Clyde", right half at $54 (T).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %001111 C, %000000 C, \ Column #1
%110000 C, %110011 C, %111111 C, %000000 C, \ Column #2
%110000 C, %110011 C, %111011 C, %000000 C, \ Column #3
%110000 C, %111111 C, %001101 C, %000000 C, \ Column #4
%110000 C, %111111 C, %001110 C, %000000 C, \ Column #5
%000000 C, %011111 C, %111111 C, %000000 C, \ Column #6
%000000 C, %111111 C, %111111 C, %000000 C, \ Column #7
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %000000 C, %000000 C, \ Column #9

\ Character "rBlinky", left half at $55 (U)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #1
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #2
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #5
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #6
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #9

\ Character "rBlinky", right half at $56 (V).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #1
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #2
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #5
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #6
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #7
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #9

\ Character "rInky", left half at $57 (W)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #1
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #2
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #5
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #6
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %110011 C, %000000 C, \ Column #9

\ Character "rInky", right half at $58 (X).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %110011 C, %000000 C, \ Column #0
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #1
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #2
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110000 C, %000000 C, \ Column #5
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #6
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #7
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #9

\ Character "rPinky", left half at $59 (Y)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #1
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #2
%111100 C, %000000 C, %000100 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110010 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110001 C, %000000 C, \ Column #5
%001100 C, %101100 C, %000000 C, %000000 C, \ Column #6
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #9

\ Character "rPinky", right half at $5A (Z).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #1
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #2
%001100 C, %101100 C, %000000 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110001 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110010 C, %000000 C, \ Column #5
%111100 C, %000000 C, %000100 C, %000000 C, \ Column #6
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #7
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #9

\ Character "rClyde", left half at $5B ([)
\ Left: colunm #0 and #1 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #0
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #1
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #2
%111100 C, %100000 C, %000000 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110001 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110010 C, %000000 C, \ Column #5
%001100 C, %001100 C, %000100 C, %000000 C, \ Column #6
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #7
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #8
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #9

\ Character "rClyde", right half at $5C (\).
\ Right: columns #8 and #9 unused.
\ Group A  Group B    Group C    Group D (top to bottom)
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #0
%000000 C, %000000 C, %110000 C, %000000 C, \ Column #1
%001100 C, %001100 C, %000000 C, %000000 C, \ Column #2
%001100 C, %001100 C, %000100 C, %000000 C, \ Column #3
%001100 C, %000000 C, %110010 C, %000000 C, \ Column #4
%001100 C, %000000 C, %110001 C, %000000 C, \ Column #5
%111100 C, %100000 C, %000000 C, %000000 C, \ Column #6
%111100 C, %000000 C, %000000 C, %000000 C, \ Column #7
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #8
%111100 C, %111111 C, %111111 C, %000000 C, \ Column #9

\ The following is twice the number of sprites (dw characters).
HERE softfont - chrdefbcnt / CONSTANT nchars

\ The following includes contributed input from Leon Wagner.
: softfont.emit ( -- )
  softfont
    nchars 0 DO           \ Iterate over character definitions
      nsixels 0 DO        \ Iterate over sixel groups
        pcmw 0 DO         \ Iterate over column definitions
          DUP I nsixels * J + + C@
          [CHAR] ? + EMIT \ Emit sixel data
        LOOP
        I nsixels 1- <> IF [CHAR] / EMIT THEN \ Group delimiter
      LOOP
      chrdefbcnt +        \ Next group
    nchars 1- I <> IF semcol.emit THEN \ Character delimiter
    LOOP
  DROP ;

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
: .cross   ( -- ) 2  .dwchar ; \ Erasable/PM
: .pmrgt   ( -- ) 4  .dwchar ; \ PM -> right
: .pmgo    ( -- ) 6  .dwchar ; \ PM gobbling
: .llc     ( -- ) 8  .dwchar ;
: .lrc     ( -- ) 10 .dwchar ;
: .hbar    ( -- ) 12 .dwchar ;
: .vbar    ( -- ) 14 .dwchar ;
: .ulc     ( -- ) 16 .dwchar ;
: .urc     ( -- ) 18 .dwchar ;
: .ppl     ( -- ) 20 .dwchar ; \ Erasable/PM
: .tdn     ( -- ) 22 .dwchar ;
: .tup     ( -- ) 24 .dwchar ;
: .trg     ( -- ) 26 .dwchar ;
: .tlf     ( -- ) 28 .dwchar ;
: .west    ( -- ) 30 .dwchar ;
: .east    ( -- ) 32 .dwchar ;
: .south   ( -- ) 34 .dwchar ;
: .north   ( -- ) 36 .dwchar ;
: .door    ( -- ) 38 .dwchar ; \ Erasable/ghosts in the pen
: .pmlft   ( -- ) 40 .dwchar ; \ PM -> left
: .pmupw   ( -- ) 42 .dwchar ; \ PM -> up
: .pmdnw   ( -- ) 44 .dwchar ; \ PM -> down
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

\ Used by PM when entering/leaving the "supercharged" state.
IFGF warnings off
: bell ( -- )
  silent ?EXIT
  default-charset-select
  7 EMIT
  custom-charset-select ;
IFGF warnings on

: initvars ( -- )
  0 serialno !          \ Entity serial number counter
  0. hiscore 2!         \ Make this somehow persistent!
  0. score  2!
  3. lives  2!          \ This is clearly overkill
  0. gamlev 2!          \ And so is this
  0. bonus  2!          \ Semantics need clarification
  0. suptim 2!          \ Semantics need clarification
  TRUE TO gm_timer_en   \ Enable ghost mode scheduler
  0 remitems# ! ;       \ Force level entry initializations

: initialize ( -- )
  initvars
  -cursor               \ Cursor off
  esc EMIT ."  F"       \ 7-bit C1 control characters
  decdld                \ Upload charset definition
  custom-charset-select \ Select custom character set
  bold-sgr ;

: finalize ( -- )
  default-charset-select       \ Select custom character set
  24 79 AT-XY CR
  +cursor               \ Cursor on
  default-sgr ;

: .var ( varaddr -- )
  2@ <# # # # # # # # # #> TYPE ;

: update-score ( -- )
  default-charset-select
  0 4  AT-XY score   .var
  custom-charset-select ;

: update-lives ( -- )
  default-charset-select
  0 7  AT-XY lives   .var
  custom-charset-select ;

: update-level ( -- )
  default-charset-select
  gamlev 2@ 1. D+ gamlev 2!
  0 10 AT-XY gamlev  .var
  custom-charset-select ;

\ TODO: this slows the game down considerably when the ghosts
\ are in the 'frightened" state because:
\ 1/ the display is updated on every clock cycle.
\ 2/ under Z79Forth, the pictured numbers code is based on
\    a very slow long division algorithm.
: update-suptim ( -- )
  default-charset-select
  clkperiod 5 / S>D suptim 2@ D+ suptim 2!
  0 16 AT-XY suptim  .var
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
  CR ." Data stack depth was " DEPTH .
  BEGIN DEPTH WHILE DROP REPEAT ;

: crash-and-burn ( exitmsg-addr exitmsg-bcnt )
  default-charset-select
  0 23 AT-XY TYPE
  CR .S
  drain +cursor
  default-sgr      \ VT340 specific code.
  QUIT ;

\ Display grid character (double width) at the current
\ cursor position.
: .grid-char ( grid-char -- )
  DUP BL = IF DROP 2 SPACES EXIT THEN

  DUP [CHAR] A [CHAR] ^ 1+ WITHIN 0= IF
    S" .grid-char: illegal character" crash-and-burn
  THEN

  case!
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
  S" CEEEEEEEEEHEEEEEEEEEEEHEEEEEEEEED" 22 display-line
  #items remitems# ! ;

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
  CFIELD: e.resurr   \ # Clock ticks till we're back (ghosts)
  CFIELD: e.reward   \ # points for killing a ghost / 100 (PM)
  CFIELD: e.vrow#    \ Virtual row number
  CFIELD: e.pcol#    \ Physical column number
  CFIELD: e.ivrow#   \ Interfering virtual row number (ghosts)
  CFIELD: e.ipcol#   \ Interfering pcol number (ghosts)
  CFIELD: e.igchr    \ Interfering grid character (ghosts)
  CFIELD: e.pcol0    \ Initial pcol number
  CFIELD: e.vrow0    \ Initial vrow number
  CFIELD: e.dir0     \ Initial direction
  CFIELD: e.hcvr#    \ Home corner vrow# (ghosts)
  CFIELD: e.hcpc#    \ Home corner pcol# (ghosts)
  CFIELD: e.cdir     \ Current direction
  CFIELD: e.pdir     \ Previous direction
  CFIELD: e.idir     \ Intended direction (PM)
  CFIELD: e.revflg   \ Reverse direction directive (ghosts)
  CFIELD: e.inited   \ TRUE if first display has been performed
  CFIELD: e.gobbling \ # Clock ticks till we're fed (PM)
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
4 CONSTANT dir_blocked \ Must be 1 + dir_right
5 CONSTANT dir_unspec \ Invalid except for idir (pacman)
6 CONSTANT dir_quit \ Invalid except as retval/pacman.dirselect

\ Display pacman--rendition depends on the current direction
\ and gobbling status. Gobbling overrides the direction
\ indication.
: .pacman ( -- )
  pacman-addr e.gobbling C@ ?DUP IF \ S: gobbling-cycle-count
    .pmgo          \ Display pacman as gobbling
    1- pacman-addr e.gobbling C!
    EXIT
  THEN

  pacman-addr e.cdir C@ DUP dir_blocked = IF
    DROP pacman-addr e.pdir C@ \ Select 'pdir' if blocked
  THEN

  ( S: selected-dir ) case!
  dir_right case? IF .pmrgt EXIT THEN
  dir_left  case? IF .pmlft EXIT THEN
  dir_up    case? IF .pmupw EXIT THEN
  dir_down  case? IF .pmdnw EXIT THEN

  S" .pacman: invalid current direction"
    crash-and-burn ;

\ Display entity.
: entity.display ( self -- )
  e.inum C@ ?DUP IF
    case!
  ELSE
    .pacman EXIT
  THEN

  fright_timer @ IF \ Ghosts are frightened. Use reverse video
    1 case? IF .rblinky EXIT THEN
    2 case? IF .rinky   EXIT THEN
    3 case? IF .rpinky  EXIT THEN
    4 case? IF .rclyde  EXIT THEN
  ELSE              \ They are'nt. Use the regular primitives
    1 case? IF .blinky  EXIT THEN
    2 case? IF .inky    EXIT THEN
    3 case? IF .pinky   EXIT THEN
    4 case? IF .clyde   EXIT THEN
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
      \ 1: the grid character is 'T' (ghosts' pen door) AND
      \ 2: we're a ghost (i.e. not pacman) AND
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

\ Re-display an erasable that was at least partially obscured
\ by a ghost passing by.
: .interfering ( self -- )
  >R
  R@ e.igchr C@ IF
    R@ e.ipcol# C@ x0 + R@ e.ivrow# C@ >grid-space AT-XY
      R@ e.igchr C@ .grid-char
  THEN
  R> DROP ;

\ Utility routine--not a method.
: entity.reset-coords-and-dir ( self -- )
  >R
  R@ e.dir0  C@ R@ e.cdir  C!
  R@ e.vrow0 C@ R@ e.vrow# C!
  R@ e.pcol0 C@ R@ e.pcol# C!
  R> DROP ;

: .pacman-dying-routine ( -- )
  pacman-addr e.pcol# C@ x0 +
  pacman-addr e.vrow# C@ >grid-space

  4 0 DO
    dir_blocked dir_up DO
      I pacman-addr e.cdir C!
      2DUP AT-XY .pacman
      125 MS
    LOOP
  LOOP
  AT-XY 2 SPACES

  0 fright_timer !           \ PM no longer "supercharged"
  0 pacman-addr e.reward C!  \ Reset the 'reward' field

  \ Every entity returned to its original upright position.
  entvec #entities 0 DO
    DUP @
      \ Blank current entity location.
      DUP DUP e.pcol# C@ x0 +
        SWAP e.vrow# C@ >grid-space AT-XY 2 SPACES

      \ Restore potentiallly obscured character.
      DUP .interfering

      \ Also clear the possible interference record.
      DUP e.igchr FALSE SWAP C!

      I IF  \ Keep the ghosts mostly harmless for a little time
        DUP e.resurr 20 SWAP C!
      THEN

      \ Generic death handling.
      DUP entity.reset-coords-and-dir
      e.inited FALSE SWAP C!
    CELL+
  LOOP DROP ;

\ Debugging support.
: debug-enter ( -- )
  default-charset-select
  0 23 AT-XY 78 SPACES
  0 23 AT-XY ;

: debug-leave ( -- )
  custom-charset-select
  KEY DROP ;

: ghost.debug-print ( pcol-new vrow-new debug-tag-char self )
  ( -- pcol-new vrow-new )
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

  dir_unspec ;     \ No comprendo

: pacman.stepped-on? ( ghost-inst -- flag )
  \ Compare the grid coordinates.
  DUP e.vrow# C@ >grid-space
    SWAP e.pcol# C@ >grid-space
  pacman-addr e.vrow# C@ >grid-space
    pacman-addr e.pcol# C@ >grid-space
  D= ;

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

: only-one-dir? ( bitmap -- bitmap FALSE|dir\TRUE )
  DUP 1 = IF 0 TRUE EXIT THEN
  DUP 2 = IF 1 TRUE EXIT THEN
  DUP 4 = IF 2 TRUE EXIT THEN
  DUP 8 = IF 3 TRUE EXIT THEN
  FALSE ;

\ The following implements the frightened ghost mode.
: ghost.dirselect-fright ( self bitmap -- new-dir )
  NIP                    \ S: bitmap
  dir_blocked dir_up DO
    DUP 1 AND            \ S: bitmap\bit0(bitmap)
    SWAP 1 RSHIFT SWAP   \ S: bitmap>>1\bit0(bitmap)
    IF                   \ bit0(bitmap) is set; S: bitmap>>1
      ?DUP IF            \ There are other possible directions
        random 8 AND IF
          DROP I UNLOOP EXIT \ Select direction I
        THEN
      ELSE               \ There are no alternatives left
        I UNLOOP EXIT
      THEN
    THEN
  LOOP

  S" ghost.dirselect-fright: no viable direction found"
    crash-and-burn ;

\ For every bit set in bitmap, we need to evaluate the
\ Euclidian distance between the potential next location and
\ the target tile. Finally we return the direction that
\ minimizes the distance.
\ Note: U> is ANS94 'Core Ext', so I'm using it.
: ghost.dirselect-nav2target ( self bitmap tvr tpc )
  ( -- new-dir )
  3 ROLL 3 ROLL          \ S: tvr\tpc\self\bitmap
  0 65535                \ S: tvr\tpc\self\bitmap\minoff\minval
  dir_blocked dir_up DO
    2 PICK I bitset? IF  \ Direction I is an option
      3 PICK e.pcol# C@
      \ S: self\bitmap\minoff\minval\pc-cur
      4 PICK e.vrow# C@
      \ S: self\bitmap\minoff\minval\pc-cur\vr-cur

      I case!
      dir_left  case? IF SWAP 1- SWAP THEN
      dir_right case? IF SWAP 1+ SWAP THEN
      dir_up    case? IF 1- THEN
      dir_down  case? IF 1+ THEN
      \ S: tvr\tpc\self\bitmap\minoff\minval\pc-next\vr-next

      \ Selected target is at [tvr, tpc].
      7 PICK - DUP *
      \ S: tvr\tpc\self\bitmap\minoff\minval\pc-next\dy^2
      SWAP 6 PICK - DUP *
      \ S: self\bitmap\minoff\minval\dy^2\dx^2
      +                  \ We compare the squared distance
    ELSE
      65535              \ uint16 max
    THEN
    \ S: tvr\tpc\self\bitmap\minoff\minval\minval-new

    2DUP U> IF
      NIP            \ S: tvr\tpc\self\bitmap\minoff\minval-new
      NIP I SWAP         \ S: tvr\tpc\self\bitmap\I\minval-new
    ELSE
      DROP
    THEN
  LOOP                   \ S: tvr\tpc\self\bitmap\minoff\minval

  DROP NIP NIP NIP NIP ;

\ In scatter mode, simply navigate to the ghost home corner.
: ghost.dirselect-scatter ( self bitmap -- new-dir )
  OVER e.hcvr# C@ 2 PICK e.hcpc# C@
    ghost.dirselect-nav2target ;

: ghost.dirselect-chase ( self bitmap -- new-dir )
  \ Blinky handling. The target is PM's current location.
  OVER e.inum C@ 1 = IF
    pacman-addr e.vrow# C@ pacman-addr e.pcol# C@
    ghost.dirselect-nav2target EXIT
  THEN

  \ Pinky handling. The target is 8 half tiles in PM's
  \ current moving direction. It might be off the grid but
  \ that does not matter in the least.
  OVER e.inum C@ 2 = IF
    pacman-addr e.vrow# C@ pacman-addr e.pcol# C@

    pacman-addr e.cdir C@ case!
    dir_left  case? IF 8 - THEN
    dir_right case? IF 8 + THEN
    dir_up    case? IF SWAP 8 - SWAP THEN
    dir_down  case? IF SWAP 8 + SWAP THEN

    ghost.dirselect-nav2target EXIT
  THEN

  \ Inky handling. The target is at the end of a vector twice
  \ as long as the one originating from Blinky to PM's moving
  \ direction extrapolated by 4 half tiles.
  OVER e.inum C@ 3 = IF
    pacman-addr e.vrow# C@ pacman-addr e.pcol# C@

    pacman-addr e.cdir C@ case!
    dir_left  case? IF 4 - THEN
    dir_right case? IF 4 + THEN
    dir_up    case? IF SWAP 4 - SWAP THEN
    dir_down  case? IF SWAP 4 + SWAP THEN

    entvec CELL+ @ DUP \ S: pmvr+\pmpc+\blinky-addr\blinky-addr
    e.pcol# C@ ROT - 2* \ S: pmvr+\blinky-addr\dx*2
    SWAP                \ S: pmvr+\dx*2\blinky-addr
    e.vrow# C@ ROT - 2* \ S: dx*2\dy*2

    \ The relative displacement refers to Blinky's current pos.
    entvec CELL+ @ DUP e.pcol# C@ SWAP e.vrow# C@ SWAP
    D+                  \ Two birds with the same stone
    ghost.dirselect-nav2target EXIT
  THEN

  \ Default policy. Will only apply to Clyde--permanently
  \ frightened in chase mode.
  ghost.dirselect-fright ;

\ From the "pacman dossier:"
\ "Ghosts are forced to reverse direction by the system anytime
\ the mode changes from: chase-to-scatter, chase-to-frightened,
\ scatter-to-chase, and scatter-to-frightened. Ghosts do not
\ reverse direction when changing back from frightened to chase
\ or scatter modes."
\
\ Interpreting the gospel:
\ - 'reversing direction' means selecting opposite(cdir).
\
\ The direction returned is guaranteed to be adopted by the
\ caller.
: ghost.dirselect ( self -- new-dir )
  \ No direction changes unless both vrow# and pcol# are even.
  DUP e.vrow# C@ 1 AND IF e.cdir C@ EXIT THEN
  DUP e.pcol# C@ 1 AND IF e.cdir C@ EXIT THEN

  %1111                  \ The sum of 'a priori' alternatives
  OVER e.revflg C@ DUP >R IF
    OVER e.revflg 0 SWAP C!
  ELSE
    OVER e.cdir C@
      2 + 3 AND
      bitclear           \ Exclude opposite(cdir)
  THEN                   \ S: self\bitmap
  R> -ROT                \ S: revflg\self\bitmap

  dir_blocked dir_up DO
    DUP I bitset? IF     \ Direction I is 'a priori' viable
      OVER I can-move-in-dir? \ Check for a possible obstacle
      0= IF              \ Blocked in direction I
        I bitclear
      THEN
    THEN
  LOOP

  debug 2 AND IF
    debug-enter  ." bitmap: " DUP .  debug-leave
  THEN

  \ If we are inside of the ghosts' pen and the current
  \ direction remains open, ignore revflg and stick to that.
  OVER in-ghosts-pen? IF \ S: revflg\self\bitmap
    OVER e.cdir C@       \ S: revflg\self\bitmap\cdir
    2DUP bitset? IF      \ S: revflg\self\bitmap\cdir
      NIP NIP NIP EXIT
    ELSE
      DROP
    THEN
  THEN                   \ S: revflg\self\bitmap

  ROT IF                 \ Direction reversal is requested
    DROP e.cdir C@       \ S: cdir
      2 + 3 AND          \ S: opposite(cdir)
    EXIT
  THEN                   \ S: self\bitmap

  \ Optimization: if bitmap is a power of two--only one
  \ direction is viable--return this direction immediately.
  only-one-dir? IF       \ S: self\bitmap\new-dir
    NIP NIP EXIT
  THEN

  gm_cur case!
  mode_fright  case? IF ghost.dirselect-fright  EXIT THEN
  mode_scatter case? IF ghost.dirselect-scatter EXIT THEN
  mode_chase   case? IF ghost.dirselect-chase   EXIT THEN

  S" ghost.dirselect: unsupported ghost mode"
    crash-and-burn ;

\ Utility routine--not a method.
: entity.initial-display ( self -- )
  >R
  R@ e.pcol# C@ x0 +
    R@ e.vrow# C@ >grid-space
    AT-XY  R@ DUP e.display ::
  R> DROP ;

\ Utility routine--not a method.
: entity.get-new-coordinates ( self -- pcol vrow )
  >R

  \ Handling a resurrecting/grounded ghost
  R@ e.resurr C@ ?DUP IF
    1- R@ e.resurr C!
    R@ e.pcol# C@ R@ e.vrow# C@ \ Return current coordinates
    R> DROP EXIT
  THEN

  R@ e.cdir C@ case!
  R@ e.pcol# C@ R@ e.vrow# C@
  dir_left    case? IF SWAP 1- SWAP THEN
  dir_right   case? IF SWAP 1+ SWAP THEN
  dir_up      case? IF 1- THEN
  dir_down    case? IF 1+ THEN
  \ dir_blocked (PM only): fall through.

  R> DROP ;

\ Utility routine--not a method.
\ Do not preserve erasables. Manage gobbling aspect. This
\ requires an update to 'grid'. Update the score accordingly.
: pacman.moving-policy ( pcol-new vrow-new self --
    pcol-new vrow-new )
  >R
  OVER 1 AND 0=        \ pcol-new is even
  OVER 1 AND 0= AND IF \ and so is vrow-new
    2DUP get-grid-char DUP
    scorable? IF       \ Cross or pellet
      2 R@ e.gobbling C!  \ Gobble for two clock cycles

      case! score DUP 2@
      cross case? IF 10. THEN
      pellet case? IF  \ Enter "supercharged" mode
        \ Note: we do not reset the 'reward' field here.
        \ Maybe we should--or not. This is a possible way
        \ to achieve wicked scores!!!
        super-enter
        50.
      THEN
      D+ ROT 2!
      update-score

      \ Cross or pellet consumed. Blank the grid character.
      2DUP get-grid-char-addr BL SWAP C!

      remitems# @ ?DUP IF
        1- remitems# !
      THEN
    ELSE
      DROP
    THEN
  THEN

  R> DROP ;

\ Utility routine--not a method.
\ Preserve erasables.
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

\ Utility routine--not a method.
: collision-handle ( pcol-new vrow-new onproc ghost-addr -- )
  ( pcol-new vrow-new )
  \ Make sure the entity at TOS is a ghost.
  DUP e.inum C@ 1 #ghosts 1+ WITHIN 0= IF
    S" collision-handle: not a ghost on TOS" crash-and-burn
  THEN

  SWAP >R            \ Backup 'onproc'
  \ S: pcol-new\vrow-new\ghost-addr, R: onproc

  fright_timer @ IF
    \ The ghost at TOS dies--unless it is resurrecting.
    \ Note: only Blinky resurrects outside of the pen.
    DUP e.resurr C@ 0= IF
      DUP .interfering
      0 OVER e.igchr C!   \ Clear interference record

      50 OVER e.resurr C! \ Ghost grounded for 50 clk cycles

      \ Update the score based on the 'reward' field.
      pacman-addr e.reward C@ ?DUP IF
        2*
      ELSE
        2            \ 200 is the payoff for the first kill
      THEN
      DUP pacman-addr e.reward C!
      100 * S>D score 2@ D+ score 2! update-score

      DUP entity.reset-coords-and-dir
      \ S: pcol-new\vrow-new\ghost-addr

      \ Ghost returned to the pen.
      R@ IF          \ If the ghost just killed was ONPROC
        NIP NIP      \ Drop anticipated ghost coordinates
        DUP e.pcol# C@ SWAP e.vrow# C@
      ELSE
        DROP         \ S: pcol-new\vrow-new
      THEN
    ELSE
      DROP           \ S: pcol-new\vrow-new
    THEN
  ELSE               \ PM dies
    \ S: pcol-new\vrow-new\ghost-addr, R: onproc
    .pacman-dying-routine

    lives 2@ -1. D+ lives 2! \ Decrement 'lives' (a double)
    update-lives             \ and update the display

    lives 2@ D0= IF
      S" collision-handle: game over!" crash-and-burn
    THEN

    \ If R@ is FALSE, PM was ONPROC and we need to update
    \ pcol-new\vrow-new to match PM's coordinates post mortem.
    R@ 0= IF
      DROP 2DROP
      pacman-addr e.pcol# C@  pacman-addr e.vrow# C@
    ELSE
      \ A ghost is ONPROC and is responsible for PM's death.
      NIP NIP
      DUP e.pcol# C@ SWAP e.vrow# C@
    THEN
  THEN

  R> DROP ;

\ Entity method.
: entity.move ( self -- )
  >R

  R@ e.inited C@ 0= IF \ If this is the first display request.
    R@ entity.initial-display
    TRUE R> e.inited C! EXIT
  THEN

  \ 'cdir' validation.
  R@ e.cdir C@ dir_up dir_blocked 1+ WITHIN 0= IF
    S" entity.move: illegal current direction" crash-and-burn
  THEN
  \ dir_blocked should only be in effect for PM, which
  \ is an indication that some keyboard input is required.
  R@ e.cdir C@ dir_blocked =
  R@ e.inum C@ 0<> AND IF
    S" entity.move: ghost blocked!!!" crash-and-burn
  THEN

  R@ DUP DUP e.inum C@ IF
    ghost.dirselect
  ELSE
    pacman.dirselect
  THEN
  SWAP e.cdir C!

  -1 -1 [CHAR] A R@ ghost.debug-print 2DROP

  \ Blank current position on screen.
  R@ e.pcol# C@ x0 + R@ e.vrow# C@ >grid-space AT-XY 2 SPACES

  \ Update entity's coordinates on the data stack.
  R@ entity.get-new-coordinates \ S: pcol-new\vrow-new

  [CHAR] B R@ ghost.debug-print

  R@ DUP e.inum C@ IF    \ S: pcol-new\vrow-new\self
    ghost.moving-policy
  ELSE
    pacman.moving-policy
  THEN
  \ S: pcol-new\vrow-new

  [CHAR] F R@ ghost.debug-print

  \ Update entity's coordinates fields.
  2DUP  R@ e.vrow# C!  R@ e.pcol# C!

  \ Collision handling.
  R@ e.inum C@ IF        \ A ghost is ONPROC
    R@ pacman.stepped-on?
    R@
  ELSE                   \ PM is ONPROC
    \ We have to check all possible ghosts' coordinates.
    FALSE entvec CELL+ #ghosts 0 DO
      DUP @ pacman.stepped-on? IF
        NIP TRUE SWAP LEAVE
      ELSE
        CELL+
      THEN
    LOOP
    OVER IF @ THEN
  THEN
  SWAP \ S: pcol-new\vrow-new\ghost-addr\flag

  IF ( pcol-new\vrow-new\ghost-addr )
    \ Pass on whether the colliding ghost is ONPROC.
    DUP R@ = SWAP collision-handle
  ELSE
    DROP
  THEN
  \ S: pcol-new\vrow-new

  \ Display entity at new coordinates.
  SWAP x0 + SWAP >grid-space AT-XY R@ DUP e.display ::

  -1 -1 [CHAR] G R@ ghost.debug-print 2DROP

  R> DROP ;

\ Entity constructor.
: entity.new ( "name" -- address; hcvr hcpc vrow pcol cdir -- )
  CREATE
    entity ALLOT
  DOES>            \ vrow\pcol\cdir\address
    >R             \ vrow\pcol\cdir, R: address
    \ Initialize default valued fields.
    ['] entity.move    R@ e.strategy !
    ['] entity.display R@ e.display  !
    0                  R@ e.resurr   C!
    0                  R@ e.reward   C!
    0                  R@ e.ivrow#   C!
    0                  R@ e.ipcol#   C!
    0                  R@ e.igchr    C!
    dir_blocked        R@ e.pdir     C!
    dir_unspec         R@ e.idir     C!
    FALSE              R@ e.inited   C!
    0                  R@ e.gobbling C!
    FALSE              R@ e.revflg   C!
    serialno @ DUP     R@ e.inum     C!
      1+ serialno !
    \ Initialize fields from arguments.
    DUP R@ e.dir0  C! R@ e.cdir  C! \ hcvr\hcpc\vrow\pcol
    DUP R@ e.pcol0 C! R@ e.pcol# C! \ hcvr\hcpc\vrow
    DUP R@ e.vrow0 C! R@ e.vrow# C! \ hcvr\hcpc
    \ Register home corner details--only relevant for ghosts.
    R@ e.hcpc# C!                   \ hcvr
    R@ e.hcvr# C!                   \ --
    R> ;           \ Return 'address'

entvec
  \ By convention, we have PM as instance #0.
  \ This is a central assumption though!
  entity.new pacman
  $FF $FF 34 32 dir_right pacman
  OVER ! CELL+

  entity.new blinky          \ Entity #1, Red, default design
  4 60 14 32 dir_left blinky \ North central ghost
  OVER ! CELL+

  entity.new pinky           \ Entity #2, Pink, frowning
  4 2 20 32 dir_up pinky     \ Central ghost
  OVER ! CELL+

  entity.new inky            \ Entity #3, Cyan, nosy
  40 62 20 30 dir_down inky  \ Western ghost
  OVER ! CELL+

  entity.new clyde           \ Entity #4, Orange, smiling
  40 2 20 34 dir_left clyde  \ Eastern ghost
  OVER ! CELL+
DROP                         \ Last defined entity

\ -------------------------------------------------------------
\ Ghost mode logic is time based but there's more to it than
\ just time. When PM becomes "supercharged" the ghosts
\ transition to the frightened state for some time.

IFGF 2VARIABLE utime0

0 VALUE gm_seqno
VARIABLE gm_timer
VARIABLE _fright_timer

\ The ghost mode scheduling table.
CREATE gm_sched
\           L1      L2-4    L5+     seqno
( Scatter ) 7 ,     7 ,     5 ,     \ 0
( Chase   ) 20 ,    20 ,    20 ,    \ 1
( Scatter ) 7 ,     7 ,     5 ,     \ 2
( Chase   ) 20 ,    20 ,    20 ,    \ 3
( Scatter ) 5 ,     5 ,     5 ,     \ 4
( Chase   ) 20 ,    1033 ,  1037 ,  \ 5
( Scatter ) 5 ,     1 ,     1 ,     \ 6
( Chase   ) -1 ,    -1 ,    -1 ,    \ 6+ -> forever

: gm_timer-initval-get ( level seqno -- clkcount )
  3 * SWAP          \ seqno*3\level
  DUP 1 = IF
    DROP 0
  ELSE
    DUP 5 < IF
      DROP 1
    ELSE
      DROP 2
    THEN
  THEN
  + CELLS gm_sched + @
  DUP -1 = ?EXIT
  1000 clkperiod */ ;

: gm_seqno-getnext ( -- gm_seqno-next )
  gm_seqno DUP 6 < IF 1+ EXIT THEN
  DROP 7 ;          \ The sequence number is capped at 7

\ Called after a context change (sequence number or game level)
: gm-getnext ( -- mode )
\ Debugging code begins.
\ FALSE TO gm_timer_en
\ mode_chase
\ EXIT
\ Debugging code ends.

  gamlev 2@ D>S gm_seqno gm_timer-initval-get
  DUP -1 <> DUP TO gm_timer_en IF
    gm_timer !
    gm_seqno 1 AND IF mode_chase ELSE mode_scatter THEN
    EXIT
  THEN
  DROP mode_chase ;

: gm_prv-update ( -- )
  gm_cur mode_fright = ?EXIT
  gm_cur TO gm_prv ;

: .mode ( mode -- )
  case!
  mode_scatter case? IF ." SCATTER" EXIT THEN
  mode_chase   case? IF ." CHASE  " EXIT THEN
  mode_fright  case? IF ." FRIGHT " EXIT THEN
  ." UNSPEC " ;

: .gm-sitrep ( -- )
  CR
  \ If operating under GNU Forth, include timing information.
IFGF [CHAR] [ EMIT
IFGF utime utime0 2@ DNEGATE D+ DROP 1000 / \ Convert to MS
IFGF 100 / \ Convert to tenth of seconds
IFGF S>D <# # [CHAR] . HOLD # # # [CHAR] , HOLD # # # #>
IFGF TYPE [CHAR] ] EMIT SPACE
    ." cur: " gm_cur .mode SPACE
    ." prv: " gm_prv .mode SPACE
    ." gl#: " gamlev 2@ D>S 2 .R SPACE
    ." sn#: " gm_seqno .
    ." ten: " gm_timer_en 2 .R SPACE
    ." gmt: " gm_timer @  4 .R
  ;

\ All ghosts adopt the direction opposite to the current one.
: gm-allghosts-reverse ( -- )
  entvec CELL+ #ghosts 0 ?DO
    DUP @ e.revflg TRUE SWAP C!
    CELL+
  LOOP DROP bell ;

\ In any given level, this should be called only after
\ level-entry-inits.
: gm-switchto ( mode -- )
  DUP gm_cur = IF   \ Current mode is not changing
    DROP EXIT
  THEN

  \ If switching away from chase or scatter modes, signal
  \ direction reversal request to all ghost instances.
  gm_cur mode_fright <> IF gm-allghosts-reverse THEN

  gm_prv-update
  TO gm_cur ;

: _super-enter ( -- )
  gm-allghosts-reverse             \ HackerB9's request

  \ We might want to EXIT immediately depending on 'gamlev'
  gm_cur mode_fright = IF          \ Already frightened
    super-clkcycles fright_timer ! \ Be kind, reset the timer!
    EXIT
  THEN

  gm_prv-update
  mode_fright TO gm_cur
  FALSE TO gm_timer_en             \ Suspend gm_timer
  super-clkcycles fright_timer ! ; \ Enable the 'fright' timer

: _super-leave ( -- )
  0 pacman-addr e.reward C! \ Reset ghost kill counter
  gm_prv gm-switchto
  TRUE TO gm_timer_en ;            \ Re-enable gm_timer

\ -------------------------------------------------------------
\ Reset all entities coords/dir and set 'inited' to FALSE.
\ Also clear 'fright_timer' and PM's 'reward' field.
\ Reset the PRNG's seed to a fixed value, as per the gospel.

: level-entry-inits ( -- )
  pacman-addr entity.reset-coords-and-dir
  FALSE pacman-addr e.inited C!
  0 pacman-addr e.reward C!

  entvec CELL+ #ghosts 0 ?DO
    DUP @
      DUP entity.reset-coords-and-dir
      e.inited FALSE SWAP C!
    CELL+
  LOOP DROP

  23741 seed !

  \ Ghost mode level entry initializations.
  IFGF utime utime0 2!
  0 fright_timer !
  0 TO gm_seqno
  gm-getnext  TO gm_cur
  mode_unspec TO gm_prv ;

\ -------------------------------------------------------------
\ Entry point here.

: _main ( -- )
  BEGIN
\   DEPTH IF S" WTF?" crash-and-burn THEN
    remitems# @ 0= IF      \ If remitems# is 0, start new level
      .initial-grid
      update-level
      level-entry-inits
      tty-drain
    ELSE
      \ Ghost mode handling.
      gm_cur mode_fright = IF
        fright_timer @ ?DUP IF \ Continue w/ frightened ghosts
          1- fright_timer !
          update-suptim
        ELSE
          super-leave
        THEN
      ELSE
        gm_timer_en IF
          gm_timer @ ?DUP IF
            1- gm_timer !           \ Ghost mode unchanged
          ELSE
            gm_seqno-getnext TO gm_seqno
            gm-getnext gm-switchto  \ Re-compute gm parameters
          THEN
        THEN
      THEN

      \ Regular entity scheduling.
      entvec #entities 0 DO
        DUP @ DUP e.strategy ::  \ Move current entity
        CELL+
      LOOP DROP

      clkperiod MS
    THEN
  AGAIN ;

: main ( -- )
  entvec @ TO pacman-addr
  ['] _fright_timer IS fright_timer
  ['] _super-enter  IS super-enter
  ['] _super-leave  IS super-leave
  initialize
  PAGE .init-sitrep \ Initial scoreboard

  IFZ7 _main finalize
  IFGF ['] _main CATCH finalize
  IFGF ?DUP IF
  IFGF   0 23 AT-XY ." Caught exception " DUP . CR
  IFGF   ." Depth was " DEPTH . CR
  IFGF   THROW      \ We still want a stack dump!
  IFGF THEN
;

main

\ wasteit

