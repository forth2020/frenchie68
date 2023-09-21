\ Hexadoku Solver. Z79Forth/A. Francois Laagel.    May 11, 2023

\ The interesting thing about this algorithm is that is does
\ not work by looking for a solution. It works by systematic
\ refutation of possibilities leading to constraint violations.
\ Eventually, a solution might emerge--or not. There could be
\ several solutions to a weakly defined problem but this is
\ not addressed by this code. It will stop when the first one
\ is encountered.
\
\ This code targets Z79Forth (2 byte cell). It can also be run
\ under GNU Forth 0.7.3 (8 byte cell).
\
\ "[Agent Smith] Never send a human to do a machine's job."
\ from "The Matrix" movie, 1999.

\ -------------------------------------------------------------
\ Glossary:
\
\ grid: a 16 row by 16 columns structure consisting of spots.
\
\ spot: an unsigned 16 bit integer (stored as a cell) that
\ represents either:
\ - a resolved term for the hexadecimal number residing at
\   the corresponding location. A resolved term is an exact
\   power of two, i.e. only one bit is set for that spot.
\ - or the logical sum of possible values for that spot.
\   This would be the sum of all possibilities, in quantum
\   theory terms. Such a number has more than one bit set.
\
\ fixed point: a grid cell that is resolved, i.e. has a
\ provisional value that is a power of two (non-zero). Such a
\ cell value cannot be altered by mask application/filtering.
\
\ transaction: a set of saved states made immediately prior
\ to an original speculative decision and all subsequently
\ inferred changes before a dead end situation is detected.
\ This is the basis for an undo log buffer (aka transaction
\ stack).
\
\ A spot having zero for its value indicates a dead end in the
\ current problem resolution state. This program strives to
\ behave so as to avoid that from ever happening.

\ -------------------------------------------------------------
DECIMAL
MARKER wasteit

: gf? 1 CELLS 8 = ;            \ TRUE if GNU Forth

: IFZ7 [ gf?    ] LITERAL IF POSTPONE \ THEN ;
: IFGF [ gf? 0= ] LITERAL IF POSTPONE \ THEN ;

\ Following code block borrowed from GNU Forth 0.7.3 vt100.fs.
IFZ7 : pn    BASE @ SWAP DECIMAL 0 U.R BASE ! ;
IFZ7 : ;pn   [CHAR] ; EMIT pn ;
IFZ7 : ESC[  #27 EMIT [CHAR] [ EMIT ;
IFZ7 : AT-XY 1+ SWAP 1+ SWAP ESC[ pn ;pn [CHAR] H EMIT ;

IFZ7 : machdep-wait ;
IFZ7 : CELL/ 1 RSHIFT ;
IFZ7 : 2CELLS/ 2 RSHIFT ;

IFGF : machdep-wait ( 1 MS ) ; \ For visual effect only!
IFGF : CELL/ 3 RSHIFT ;
IFGF : 2CELLS/ 4 RSHIFT ;

: 16* 4 LSHIFT ;
: 16/MOD DUP $F AND SWAP 4 RSHIFT ;
: 1+! 1 SWAP +! ;
: 1-! -1 SWAP +! ;

\ -------------------------------------------------------------
\ Variables and constants.

FALSE VALUE logtrans   \ If NZ, log changes to the trans. stack
BL CONSTANT wildc
VARIABLE unknowns

CREATE grid 256 CELLS ALLOT    \ 16x16 is the problem size

\ A transaction is the unit of rollbacks (undos). It is defined
\ as the set of grid changes between the time we make a
\ speculative choice and the present time or the time of a
\ nested speculative choice (excluded).
\ In general terms a transaction starts with a speculation
\ and includes all the inferred changes to the grid--possibly
\ up to an impossible situation, leading to a backtrack.

4096 CONSTANT tstk-nitems
CREATE tstack tstk-nitems 2* CELLS ALLOT
HERE CONSTANT tstk-bottom
\ Each entry on the transaction stack is:
\ TOS:  saved-bitmask		1 CELL
\ TOS+1: mxxx.xxxx:yyyy.yyyy	1 CELL
\ 	bit #15:	beginning of transaction marker.
\ 	bits #14-8:	xcol: 0..15
\ 	bit #7-0:	yrow: 0..15
VARIABLE tstkp

\ Statistical data support.

VARIABLE reclev                \ Current recursion level
VARIABLE reclevmax             \ Maximum recursion level
VARIABLE nbt                   \ # of backtracks
CREATE ncb 2 CELLS ALLOT       \ # of calls to countbits double

: D1+! DUP 2@ 1. D+ ROT 2! ;

\ -------------------------------------------------------------
\ Adapted from "Hacker's Delight" Second Edition
\ by Henry S. Warren Jr., Edt by Addison-Wesley
\ Chapter 5 "Counting bits", page 82.

: _countbits ( uu -- #bits )
  DUP 1 RSHIFT $5555 AND -
  DUP $3333 AND SWAP 2 RSHIFT $3333 AND +
  DUP 4 RSHIFT + $0F0F AND
  DUP 8 RSHIFT +
  $1F AND ;
: countbits ncb d1+! _countbits ;

: 2^n ( n -- 2^n ) 1 SWAP LSHIFT ;

\ -------------------------------------------------------------
\ Incremental grid visualization.

: |visual ( val saddr -- val saddr )
  OVER 0= ABORT" New value is 0!"

  OVER countbits 1 <> IF
    wildc
  ELSE                         \ Slot value is known
    OVER 16 0 DO
      DUP I 2^n = IF
        DROP I
        DUP 10 < IF [CHAR] 0 ELSE [CHAR] 7 THEN
        + LEAVE
      THEN
    LOOP
  THEN

  \ S: val\saddr\char-from-val
  \ Return immediately if char==wildc and bitcount(saddr@)<>1
  \ This corresponds to a situation where a given cell's mask
  \ changes but the spot remains unresolved.
  OVER @ countbits 1 <> OVER wildc = AND IF
    DROP EXIT
  THEN

  \ Now to convert 'saddr' to x,y.
  OVER grid - CELL/ 16/MOD   \ S: val\saddr\char-from-val\x\y
  SWAP 2* SWAP AT-XY EMIT machdep-wait ;

\ -------------------------------------------------------------
\ Transaction stack handling (undo log).

: CELL- 1 CELLS - ;

: tstk-push ( begin-flag ptr -- )
  \ We need exactly two cells. Is enough room available?
  tstkp @ tstack - 2CELLS/ 0=
    ABORT" Transaction stack overflow"

  \ Extract x and y from the 'ptr' pointer.
  DUP >R
  grid - CELL/ 16/MOD          \ S: begin-flag\x\y
  SWAP ROT                     \ S: y\x\begin-flag
  IF $80 OR THEN
  8 LSHIFT OR

       tstkp @ CELL- DUP tstkp ! !
  R> @ tstkp @ CELL- DUP tstkp ! ! ;

: tstk-pop ( -- begin-flag )
  \ At least two cells need to be stacked up.
  tstk-bottom tstkp @ - 2CELLS/ 0=
    ABORT" Transaction stack underflow"

  tstkp @ DUP @ >R             \ R: bitmsk, S: tsktp@
  CELL+ tstkp !

  tstkp @ DUP @ >R             \ R: bitmsk\mX:Y, S: tsktp@
  CELL+ tstkp !

  R> DUP $8000 AND             \ R: bitmsk, S: mX:Y\beg-flg
  SWAP $7FFF AND               \ R: bitmsk, S: beg-flg\X\Y

  DUP 8 RSHIFT SWAP $FF AND    \ R: bitmsk, S: beg-flg\X\Y
  16* + CELLS grid +           \ R: bitmsk, S: beg-flg\saddr
  R> SWAP                      \ S: beg-flg\bitmsk\saddr

  \ Check whether we are going from resolved to unresolved.
  \ If so increment 'unknowns' accordingly.
  DUP @ countbits 1 = IF       \ S: beg-flg\bitmsk\saddr
    OVER countbits 1 > IF
      unknowns 1+!
    THEN
  THEN

  |visual ! ;                  \ Implicit update-spot

\ -------------------------------------------------------------
\ Initializations.

: char>digit ( char -- char|digitval )
  DUP [CHAR] 0 [CHAR] 9 1+ WITHIN IF [CHAR] 0 - EXIT THEN
  DUP [CHAR] A [CHAR] F 1+ WITHIN IF [CHAR] 7 - THEN ;

: initline ( srcaddr bytecount linenum -- )
  16* CELLS grid +             \ S: srcaddr\bytecount\tgtaddr
  SWAP 0 DO                    \ S: srcaddr\tgtaddr
    OVER I + C@ char>digit DUP 16 < IF
      2^n                      \ S: srcaddr\tgtaddr\2^<digit>
      OVER !                   \ S: srcaddr\tgtaddr
      CELL+                    \ S: srcaddr\tgtaddr-next
      unknowns 1-!
    ELSE
      [CHAR] : <> IF CELL+ THEN
    THEN
  LOOP 2DROP ;

: inits ( -- )
  256 unknowns !
  grid 256 0 DO
    DUP $FFFF SWAP !
    CELL+
  LOOP
  DROP

  \ Empty grid.
\ S" ....:....:....:...." 0  initline
\ S" ....:....:....:...." 1  initline
\ S" ....:....:....:...." 2  initline
\ S" ....:....:....:...." 3  initline

\ S" ....:....:....:...." 4  initline
\ S" ....:....:....:...." 5  initline
\ S" ....:....:....:...." 6  initline
\ S" ....:....:....:...." 7  initline

\ S" ....:....:....:...." 8  initline
\ S" ....:....:....:...." 9  initline
\ S" ....:....:....:...." 10 initline
\ S" ....:....:....:...." 11 initline

\ S" ....:....:....:...." 12 initline
\ S" ....:....:....:...." 13 initline
\ S" ....:....:....:...." 14 initline
\ S" ....:....:....:...." 15 initline

  \ Elektor data set from the May/June, 2023 issue.
  S" E2.A:0..B:.F.C:649." 0  initline
  S" .C.F:158.:...0:.BA7" 1  initline
  S" ..1.:..4.:....:.8.2" 2  initline
  S" 834.:..CD:.7BE:.01." 3  initline

  S" ..F8:....:...3:..29" 4  initline
  S" 7.23:..1.:..9B:D..A" 5  initline
  S" .6..:.D.8:.AE.:5..." 6  initline
  S" .1..:5..6:.8.D:...." 7  initline

  S" .7..:A..3:.E.6:...." 8  initline
  S" .D..:.6.2:.B3.:8..." 9  initline
  S" 3.96:..5.:..7F:1..0" 10 initline
  S" ..05:....:...9:..76" 11 initline

  S" 09E.:..2A:.3F5:.C6." 12 initline
  S" ..7.:..6.:....:.5.3" 13 initline
  S" .8.C:F73.:...1:.D0B" 14 initline
  S" 5F.4:8..0:.6.2:A7E." 15 initline

  \ Elektor data set from the July/August, 2023 issue.
\ S" D.16:0.27:.A..:...B" 0  initline
\ S" .3..:....:0182:7..." 1  initline
\ S" 5.F.:...4:3B.D:..0A" 2  initline
\ S" A...:.35.:...F:..4." 3  initline

\ S" 3...:4..1:9C..:E..." 4  initline
\ S" ...1:.B..:6...:.C8." 5  initline
\ S" 6..5:..90:A8..:.DF." 6  initline
\ S" 0.A.:C.D.:..1.:4567" 7  initline

\ S" .D6.:84F.:.E..:2..." 8  initline
\ S" 2E8.:5.0.:74..:61.." 9  initline
\ S" .F..:...6:..2B:..5." 10 initline
\ S" .504:....:..9.:C.E8" 11 initline

\ S" .6..:9..3:C7.0:...." 12 initline
\ S" ....:.542:.9..:...." 13 initline
\ S" ..52:.0EA:..D8:..B." 14 initline
\ S" 8.9.:...F:...4:...6" 15 initline

  \ Elektor data set from the HS #4, 2023 issue.
  \ Solved by inference only. No speculation required!!!
\ S" F02C:D1..:..48:E75A" 0  initline
\ S" .3.9:E4F.:.5CD:6.8." 1  initline
\ S" 4A6.:....:....:.31D" 2  initline
\ S" 8...:9..A:6..1:...F" 3  initline

\ S" ..AE:..0F:B9..:CD.." 4  initline
\ S" 063.:1.47:DF.E:.5B9" 5  initline
\ S" .B.F:.D.5:C.2.:3.7." 6  initline
\ S" ..C.:.3..:..8.:.F.." 7  initline

\ S" ..D.:.A..:..6.:.0.." 8  initline
\ S" .C.2:.8.E:0.B.:1.A." 9  initline
\ S" 79B.:4.63:81.2:.CE5" 10 initline
\ S" ..01:..9D:47..:8B.." 11 initline

\ S" A...:3..2:F..B:...7" 12 initline
\ S" B14.:....:....:.89C" 13 initline
\ S" .E.7:6BD.:.A90:4.2." 14 initline
\ S" D290:7F..:..EC:5A6B" 15 initline

  \ Elektor data set from the September/October, 2023 issue.
  \ Solved by inference only. No speculation required!!!
\ S" ..E3:FB.5:8.26:40.." 0  initline
\ S" B...:.EA.:.59.:...3" 1  initline
\ S" 4...:.209:E7B.:...D" 2  initline
\ S" .7..:....:....:..5." 3  initline

\ S" 9.BE:74..:..81:32.C" 4  initline
\ S" ..46:9.CA:0B.7:DF.." 5  initline
\ S" 7.AD:8.B.:.4.2:56.1" 6  initline
\ S" 58..:D02.:.36A:..B4" 7  initline

\ S" 63..:B57.:.EAC:..80" 8  initline
\ S" 8.01:E.3.:.6.5:9B.A" 9  initline
\ S" ..DB:4.62:3F.9:C7.." 10 initline
\ S" C.27:0A..:..4D:F3.5" 11 initline

\ S" .9..:....:....:..7." 12 initline
\ S" E...:.943:52C.:...6" 13 initline
\ S" 0...:.7F.:.AD.:...9" 14 initline
\ S" ..84:5C.B:7.F0:AD.." 15 initline

  \ Transaction stack initialization.
  tstk-bottom tstkp !
  FALSE TO logtrans

  \ Statistical data initialization.
  0. ncb 2!
  0 nbt !
  0. reclev ! reclevmax ! ;

\ -------------------------------------------------------------
\ Visualization.

\ Underline character rendition on.
: +ul ( -- ) #27 EMIT ." [4m" ;

\ Underline character rendition off.
: -ul ( #27 ) #27 EMIT ." [m" ;

\ Turn off the cursor (VT200 control sequence).
: -cursor ( -- ) #27 EMIT ." [?25l" ;

\ Turn on the cursor (VT200 control sequence).
: +cursor ( -- ) #27 EMIT ." [?25h" ;

: mask>char ( mask -- char )
  DUP countbits                \ S: mask\nbits
  1 = IF
    16 0 DO
      DUP I 2^n = IF
        DROP I UNLOOP
        DUP 10 < IF [CHAR] 0 ELSE [CHAR] 7 THEN
        + EXIT
      THEN
    LOOP
    1 ABORT" WTF?"             \ This should never be executed
  THEN
  DROP wildc ;

: grid-display ( -- )
  grid 16 0 DO                 \ J has the current row#
    16 0 DO                    \ I has the current col#
      DUP @ mask>char
        EMIT SPACE
      CELL+
    LOOP
    CR
  LOOP DROP ;

\ -------------------------------------------------------------
\ Primary way of altering a grid's spot but not the only one!
\ 'speculate' does unregistered grid changes as well.
\ The only changes we can see here are inferred. Undo
\ operations are carried out via 'tstk-pop'.

: update-spot ( val saddr -- )
  2DUP @ = IF                  \ Value not changed
    2DROP EXIT
  THEN

  \ This update resolves the spot point to by 'saddr'.
  OVER countbits 1 = IF unknowns 1-! THEN

  logtrans IF                  \ Transaction is logged
    DUP FALSE SWAP tstk-push
  THEN
  |visual ! ;

\ -------------------------------------------------------------
\ Four by four exclusion/filtering.

\ No side effects.
: getmask4 ( xcol yrow -- mask\FALSE | TRUE )
  0                            \ Sanity check
  $FFFF                        \ Initial mask
  \ S: xcol\yrow\check\mask
  4 0 DO                       \ J has dy
    4 0 DO                     \ I has dx
      3 PICK I +               \ Absolute col#
      3 PICK J + 16* +
      CELLS grid +
      @ DUP countbits 1 = IF
        \ S: xcol\yrow\check\mask\val
        ROT OVER  \ S: xcol\yrow\mask\val\check\val
        2DUP AND  \ S: xcol\yrow\mask\val\check\val\(check&val)

        IF                     \ Bit already set!!!
          2DROP 2DROP 2DROP UNLOOP UNLOOP TRUE EXIT
        THEN

        \ S: xcol\yrow\mask\val\check\val
        OR               \ S: xcol\yrow\mask\val\(check|val)
        -ROT             \ S: xcol\yrow\(check|val)\mask\val
        INVERT AND       \ S: xcol\yrow\(check|val)\(mask&~val)
      ELSE
        DROP
      THEN
    LOOP
  LOOP
  \ S: xcol\yrow\check\mask
  NIP -ROT 2DROP FALSE ;

\ If 'mask' is zero, it means that all cells in that 4x4
\ quadrant are resolved (fixed points). Just return a success
\ indication should such a condition occur.
: setmask4 ( xcol yrow mask -- failure-flag )
  ?DUP 0= IF
    2DROP FALSE EXIT
  THEN

  -ROT                         \ S: mask\xcol\yrow
  4 0 DO                       \ J has dy
    4 0 DO                     \ I has dx
      OVER I +                 \ Absolute col#
      OVER J + 16* +
      CELLS grid +             \ S: mask\xcol\yrow\saddr
      DUP @ DUP countbits 1 <> IF
        \ S: mask\xcol\yrow\saddr\sval
        4 PICK AND           \ S: mask\xcol\yrow\saddr\sval-new
        ?DUP IF
          SWAP update-spot
        ELSE \ Mask application would result in zero spot value
          2DROP 2DROP UNLOOP UNLOOP TRUE EXIT
        THEN
      ELSE
        2DROP
      THEN
      \ S: mask\xcol\yrow
    LOOP
  LOOP DROP 2DROP FALSE ;

\ 4x4 block logic: either a spot is known or the list
\ of alternatives must exclude all known spots values.
: reduce4x4 ( -- failure-flag )
  4 0 DO                       \ Iterate over rows
    4 0 DO                     \ Iterate over columns
      I 4 * J 4 *
      2DUP getmask4 IF
        2DROP UNLOOP UNLOOP TRUE EXIT
      THEN
      ( S: xcol#\yrow#\new-possibly-zero-mask ) setmask4 IF
        UNLOOP UNLOOP TRUE EXIT \ XXX removed extra 2DROP here!
      THEN
    LOOP
  LOOP FALSE ;

\ -------------------------------------------------------------
\ Horizontal exclusion/filtering.

\ No side effects.
: get-horiz-mask ( yrow -- mask\FALSE | TRUE )
  0                            \ Sanity check
  $FFFF                        \ Initial mask
  ROT 16* CELLS grid + >R      \ Beginning of row address
  16 0 DO                      \ Iterate over columns
    \ S: check\mask
    J I CELLS + @ DUP countbits 1 = IF
      \ S: check\mask\val
      ROT OVER \ S: mask\val\check\val
      2DUP AND \ S: mask\val\check\val\(check&val)

      IF                       \ Bit is already set!!!
        UNLOOP R> DROP 2DROP 2DROP TRUE EXIT
      THEN

      \ S: mask\val\check\val
      OR                       \ S: mask\val\(check|val)
      -ROT                     \ S: (check|val)\mask\val
      INVERT AND
    ELSE
      DROP
    THEN
  LOOP R> DROP NIP FALSE ;

\ If 'mask' is zero. just return a success indication.
: set-horiz-mask ( yrow mask -- failure-flag )
  ?DUP 0= IF
    DROP FALSE EXIT
  THEN

  SWAP
  16* CELLS grid +
  16 0 DO                      \ Iterate over columns
    DUP @ DUP countbits 1 <> IF
      \ S: mask\saddr\sval
      2 PICK AND               \ S: mask\saddr\sval-new
      ?DUP IF
        OVER update-spot
      ELSE \ Mask application would result in zero spot value
        2DROP UNLOOP TRUE EXIT
      THEN
    ELSE
      DROP
    THEN
    \ S: mask\saddr
    CELL+
  LOOP 2DROP FALSE ;

\ -------------------------------------------------------------
\ Vertical exclusion/filtering.

\ No side effects.
: get-vert-mask ( xcol -- mask\FALSE | TRUE )
  0                            \ Sanity check
  $FFFF                        \ Initial mask
  ROT CELLS grid + >R          \ Beginning of column address
  16 0 DO                      \ Iterate over rows
    \ S: check\mask
    J I 16* CELLS + @ DUP countbits 1 = IF
      \ S: check\mask\val
      ROT OVER                 \ S: mask\val\check\val
      2DUP AND              \ S: mask\val\check\val\(check&val)

      IF                       \ Bit is already set!!!
        UNLOOP R> DROP 2DROP 2DROP TRUE EXIT
      THEN

      \ S: mask\val\check\val
      OR                       \ S: mask\val\(check|val)
      -ROT                     \ S: (check|val)\mask\val
      INVERT AND
    ELSE
      DROP
    THEN
  LOOP R> DROP NIP FALSE ;

\ If 'mask' is zero. just return a success indication.
: set-vert-mask ( xcol mask -- failure-flag )
  ?DUP 0= IF
    DROP FALSE EXIT
  THEN

  SWAP
  CELLS grid +                 \ Beginning of column address
  16 0 DO                      \ Iterate over rows
    DUP @ DUP countbits 1 <> IF
      \ S: mask\saddr\sval
      2 PICK AND               \ S: mask\saddr\sval-new
      ?DUP IF
        OVER update-spot       \ S: mask\saddr
      ELSE \ Mask application would result in zero spot value
        2DROP UNLOOP TRUE EXIT
      THEN
    ELSE
      DROP
    THEN
    \ S: mask\saddr
    16 CELLS +
  LOOP 2DROP FALSE ;

: reduceall ( -- failure-flag )
  reduce4x4 IF                 \ Constraint violated
    TRUE EXIT
  THEN

  16 0 DO
    I get-horiz-mask IF        \ Constraint violated
      UNLOOP TRUE EXIT
    THEN
    ( S: new-possibly-zero-mask ) I SWAP set-horiz-mask IF
      UNLOOP TRUE EXIT
    THEN

    I get-vert-mask IF         \ Constraint violated
      UNLOOP TRUE EXIT
    THEN
    ( S: new-possibly-zero-mask ) I SWAP set-vert-mask IF
      UNLOOP TRUE EXIT
    THEN

  LOOP
  FALSE ;

\ -------------------------------------------------------------
\ Speculation.

: infer ( -- success-flag )
  256                          \ 'unknowns' worst case scenario
  BEGIN
    reduceall IF DROP FALSE EXIT THEN
    unknowns @ >
  WHILE
    unknowns @
  REPEAT TRUE ;

\ "[Gordon Gekko]: The point is ladies and gentlemen that
\ greed, for lack of a better word, is good." from the "Wall
\ Street" movie, 1987.
: get-unresolved ( -- grid-cell-addr | FALSE )
  grid DUP @ countbits          \ minp\minp@#bits
  OVER CELL+                    \ minp\minp@#bits\curp

  255 0 DO
    DUP @ countbits           \ minp\minp@#bits\curp\curp@#bits

    \ The newly selected minimum cannot ever be 1.
    DUP 1 > IF
      \ minp@#bits can be 1, indicating a resolved spot.
      \ If it is, accept anything but 1 as a new minimum.
      2 PICK 1 = IF           \ minp\minp@#bits\curp\curp@#bits
        2SWAP 2DROP 2DUP
      THEN

      \ minp\minp@#bits\curp\curp@#bits
      DUP 2 = IF               \ 2 as a good enough minimum.
        2SWAP 2DROP OVER LEAVE \ curp\curp@#bits\curp
      THEN

      DUP 3 PICK < IF          \ minp\minp@#bits\curp\curp@#bits
        2SWAP 2DROP OVER       \ curp\curp@#bits\curp
      ELSE
        DROP
      THEN
    ELSE
      DROP
    THEN

    CELL+                      \ minp\minp@#bits\curp
  LOOP DROP                    \ minp\minp@#bits

  \ If the minimum bit count is 1 the problem is solved.
  1 = IF DROP FALSE THEN ;

\ Increment recursion level counter and maintain the maximum.
: rl+ ( -- ) reclev 1+!
  reclev @ reclevmax @ MAX reclevmax ! ;

\ Decrement recursion level counter.
: rl- ( -- ) reclev 1-! ;

: speculate ( -- success-flag )
  rl+                          \ Increment recursion level

  get-unresolved               \ Look for an unresolved spot
  DUP 0= IF INVERT EXIT THEN   \ Problem solved

  DUP @                        \ S: saddr\sval
  \ The list of set bits in TOS indicate the possibilities
  \ for the selected spot. Explore these alternatives.
  16 0 DO
    DUP I 2^n AND IF
      OVER TRUE SWAP tstk-push \ Insert transaction boundary

      OVER I 2^n SWAP
        +ul |visual -ul
        unknowns 1-!           \ Spot provisionally resolved
        !                      \ Un-logged update-spot

      infer IF                 \ No inconsistencies detected
        RECURSE IF             \ Stop on the 1st solution found
          2DROP UNLOOP TRUE EXIT
        THEN
      THEN

      \ Backtrack up to the last transaction boundary.
      BEGIN tstk-pop UNTIL
      nbt 1+!                  \ Increment #backtracks

    THEN
  LOOP

  2DROP FALSE                  \ Dead end reached
  rl- ;                        \ Decrement recursion level

: main ( -- )
  inits
  PAGE -cursor

  grid-display
  infer DROP

  \ From here on, everything that could be inferred is in.
  TRUE TO logtrans
  IFGF utime                   \ Starting timestamp
  speculate DROP
  31 15 AT-XY

  IFGF utime 2SWAP DNEGATE D+ DROP 1000 / CR . ." ms elapsed"

  CR ." Maximum recursion level: " reclevmax ?
  CR ." Problem solved at level: " reclev ?
  CR ." 'countbits' called " ncb 2@ <# #S #> TYPE ."  times"
  CR ." Backtracked " nbt ? ." times"
  +cursor ;

main 7 EMIT wasteit

