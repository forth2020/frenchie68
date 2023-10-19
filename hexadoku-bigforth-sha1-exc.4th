\ Hexadoku Solver. Francois Laagel.                May 11, 2023

\ The interesting thing about this algorithm is that is does
\ not work by looking for a solution. It works by systematic
\ refutation of possibilities leading to constraint violations.
\ Eventually, a solution might emerge--or not. There could be
\ several solutions to a weakly defined problem.

\ This code can be operated as either a problem solver or as
\ a potential puzzle validator (solutions enumerator/counter).
\ The 'stopon1st' user tunable parameter selects which
\ behaviour is to be achieved. If TRUE, the program will act
\ as a solver, assuming that only one solution exists and
\ display the solving progress incrementally. Otherwise, it
\ will act as a puzzle verifier and only display the total
\ number of solutions it was able to come across.

\ This code targets GNU Forth 0.7.3 (8 byte cell). It can also
\ be run SwiftForth 3.12.0 (32 bit cell) or VFX Forth 64
\ 5.42.

\ "[Agent Smith] Never send a human to do a machine's job."
\ from "The Matrix" movie, 1999.

\ -------------------------------------------------------------

\ This is the combat ready "assume nothing" flavor of the
\ solver. It has extended debugging support and uses
\ exceptions to simplify the logic of the code but that will
\ take its toll, performance wise. Use it only in case you
\ really need to debug the code or the underlying
\ infrastructure!

\ -------------------------------------------------------------
\ Glossary:

\ grid: a 16 row by 16 columns structure consisting of spots.

\ spot: an unsigned 16 bit integer (stored as a cell) that
\ represents either:
\ - a resolved term for the hexadecimal number residing at
\   the corresponding location. A resolved term is an exact
\   power of two, i.e. only one bit is set for that spot.
\ - or the logical sum of possible values for that spot.
\   This would be the sum of all possibilities, in quantum
\   theory terms. Such a number has more than one bit set.

\ fixed point: a grid cell that is resolved, i.e. has a
\ provisional value that is a power of two (non-zero). Such a
\ cell value cannot be altered by mask application/filtering.

\ transaction: a set of saved states made immediately prior
\ to an original speculative decision and covering all
\ subsequently inferred changes before a dead end situation is
\ detected or a nested speculative decision is made. This is
\ the basis for an undo log buffer (aka transaction stack).

\ A spot having zero for its value indicates a dead end in the
\ current problem resolution state. This program strives to
\ behave so as to avoid that from ever happening.

\ OOB means out of bounds.

\ -------------------------------------------------------------
DECIMAL
MARKER wasteit

\ Required import for detecting duplicate solutions.
\ Please note that IF64 and IFN64 are defined over there!
S" ./sdigest-generic.4th" INCLUDED

: find79                       \ -- xt | 0; find79 <name>
  BL WORD
  DUP C@ 0= IF DROP ." Missing word name" EXIT THEN
  FIND 0= IF DROP FALSE THEN ;

: gf? [ find79 utime ] LITERAL ;      \ TRUE if GNU Forth
: sf? [ find79 SwiftForth ] LITERAL ; \ TRUE if SwiftForth
: vf? [ find79 vfxforth ] LITERAL ;   \ TRUE if VFX Forth 64

: IFGF  [ gf? 0= ]  LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFSF  [ sf? 0= ]  LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFVF  [ vf? 0= ]  LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFNVF [ vf? 0<> ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE

IFGF IF64  : cell/   3 RSHIFT ;
IFGF IF64  : 2cells/ 4 RSHIFT ;
\ A 32 bit GForth is rare but there are some out there!
IFGF IFN64 : cell/   2 RSHIFT ;
IFGF IFN64 : 2cells/ 3 RSHIFT ;

IFSF IF64  : 2cells/ 4 RSHIFT ;
IFSF IFN64 : 2cells/ 3 RSHIFT ;

IFVF : 2cells/ 4 RSHIFT ;
IFVF : 2nip 2SWAP 2DROP ;

: 16* 4 LSHIFT ;
: 16/mod DUP $F AND SWAP 4 RSHIFT ;
: 1+! 1 SWAP +! ;
: 1-! -1 SWAP +! ;

\ -------------------------------------------------------------
\ Variables and constants.

\ begin{user_tunable_parameters}

FALSE CONSTANT stopon1st       \ User tunable. No vis. if FALSE

0 CONSTANT debug
\ %1101 CONSTANT debug
\ Bits for the debug vector:
\ 0: trace speculate/backtrack/infer entry and exit.
\ 1: display data stack digests where it really matters.
\ 2: display exception information.
\ 3: display I and I' before and after calls to 'infer' in
\    'speculate'.

\ end{user_tunable_parameters}

FALSE VALUE logtrans    \ If NZ log changes to the trans. stack
BL CONSTANT wildc

\ User defined exception numbers.
10 CONSTANT zgcv_exc           \ Zero grid cell value detected
20 CONSTANT cvio_exc           \ Constraint violation detected

VARIABLE #unknown
VARIABLE #solution

CREATE grid 256 CELLS ALLOT    \ 16x16 is the problem size

\ A transaction is the unit of rollbacks (undos). It is defined
\ as a set of grid saved states between the time we make a
\ speculative choice and the time when an inconsistency is
\ detected or when a nested speculative choice is made
\ (excluded).

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
VARIABLE #backtrack            \ # of backtracks
VARIABLE #zgcv                 \ # of zero grid cell values dcd
VARIABLE #cvio                 \ # of constraint violations dcd
CREATE ncb 2 CELLS ALLOT       \ # of calls to countbits double

\ Support for duplicate solutions detection.
CREATE sol-digest0 5 CELLS ALLOT
CREATE sol-digest1 5 CELLS ALLOT

\ Declare forward reference.
DEFER update-spot

\ -------------------------------------------------------------
\ Bit count utilities.

: d1+! DUP 2@ 1. D+ ROT 2! ;

\ Adapted from "Hacker's Delight" Second Edition
\ by Henry S. Warren Jr., Edt by Addison-Wesley
\ Chapter 5 "Counting bits", page 82.
: countbits ( uu -- #bits )
  ncb d1+!
  DUP 1 RSHIFT $5555 AND -
  DUP $3333 AND SWAP 2 RSHIFT $3333 AND +
  DUP 4 RSHIFT + $0F0F AND
  DUP 8 RSHIFT +
  $1F AND ;

\ h. is standard equipment in SwiftForth and yet its behavior
\ is different between the 32 and 64 bit implementations.
\ So you will get a warning here, which can safely be ignored.
: h. ( n -- )
  BASE @ >R
  [CHAR] $ EMIT HEX U.
  R> BASE ! ;

\ Compute 2^n fast, i.e. faster than LSHIFT can do it.
\ Note: 'n' is restricted to the [0..15] range.
CREATE exptbl
1     , 2     , 4     , 8     ,
$10   , $20   , $40   , $80   ,
$100  , $200  , $400  , $800  ,
$1000 , $2000 , $4000 , $8000 ,

: 2^n ( n -- 2^n )
  DUP 0 16 WITHIN 0= IF
    CR ." 2^n: illegal argument: "
    h. ABORT
  THEN
  CELLS exptbl + @ ;

\ -------------------------------------------------------------
\ Incremental grid visualization.

: assert-valid-grid-addr ( saddr -- saddr )
  DUP grid DUP 256 CELLS + WITHIN 0= IF
    CR ." getxy-from-grid-addr: address out of bounds "
    h. ABORT
  THEN

  DUP DUP 1 CELLS 1- INVERT AND <> IF
    CR ." assert-valid-grid-addr: unaligned address "
    h. ABORT
  THEN ;

: getxy-from-grid-addr ( saddr - x y )
  assert-valid-grid-addr

  grid - cell/ 16/mod

  DUP 0 16 WITHIN 0= IF
    CR ." getxy-from-grid-addr: Y OOB: "
    h. ABORT
  THEN
  OVER 0 16 WITHIN 0= IF
    CR ." getxy-from-grid-addr: X OOB: " OVER
    h. ABORT
  THEN ;

: |visual ( val saddr -- val saddr )
  \ No visualization if looking for for multiple solutions.
  stopon1st 0= IF EXIT THEN

  OVER countbits 1 <> IF
    wildc
  ELSE                         \ Spot value is known
    OVER 16 0 DO
      DUP I 2^n = IF
        DROP I
        DUP 9 > IF 7 + THEN [CHAR] 0 +
        LEAVE
      THEN
    LOOP
  THEN

  \ val\saddr\char-from-val
  \ Return immediately if char==wildc and bitcount(saddr@)<>1
  \ This corresponds to a situation where a given cell's mask
  \ changes but the spot remains unresolved.
  OVER @ countbits 1 <> OVER wildc = AND IF
    DROP EXIT
  THEN

  OVER getxy-from-grid-addr    \ val\saddr\char-from-val\x\y

  debug IF
    CR reclev @ SPACES ." [ " . ." , " . ." ] <- " EMIT
    EXIT
  THEN

  SWAP 2* SWAP AT-XY EMIT ;

\ -------------------------------------------------------------
\ Transaction stack handling (undo log).

IFGF : cell- 1 CELLS - ;

: tstk-push ( begin-flag ptr -- )
  \ We need exactly two cells. Is enough room available?
  tstkp @ tstack - 2cells/ 0=
    ABORT" Transaction stack overflow"

  \ Extract x and y from the 'ptr' pointer.
  DUP >R
  getxy-from-grid-addr         \ R: ptr, S: begin-flag\x\y
  SWAP ROT                     \ R: ptr, S: y\x\begin-flag
  IF $80 OR THEN
  8 LSHIFT OR

       tstkp @ cell- DUP tstkp ! !
  R> @ tstkp @ cell- DUP tstkp ! ! ;

: tstk-pop ( -- begin-flag )
  \ At least two cells need to be stacked up.
  tstk-bottom tstkp @ - 2cells/ 0=
    ABORT" Transaction stack underflow"

  tstkp @ DUP @ >R             \ R: bitmsk, S: tsktp@
  CELL+ tstkp !

  tstkp @ DUP @ >R             \ R: bitmsk\mX:Y, S: tsktp@
  CELL+ tstkp !

  R> DUP $8000 AND             \ R: bitmsk, S: mX:Y\beg-flg
  SWAP $7FFF AND               \ R: bitmsk, S: beg-flg\X\Y

  DUP 8 RSHIFT SWAP $FF AND    \ R: bitmsk, S: beg-flg\X\Y
  16* + CELLS grid +           \ R: bitmsk, S: beg-flg\saddr
  R> SWAP                      \ beg-flg\bitmsk\saddr

  \ Check whether we are going from resolved to unresolved.
  \ If so increment '#unknown' accordingly.
  DUP @ countbits 1 = IF       \ beg-flg\bitmsk\saddr
    OVER countbits 1 > IF
      #unknown 1+!
    THEN
  THEN

  |visual ! ;                  \ Implicit update-spot

\ -------------------------------------------------------------
\ Initializations.

: char>digit ( char -- char | digitval )
  DUP [CHAR] 0 [CHAR] 9 1+ WITHIN IF [CHAR] 0 - EXIT THEN
  DUP [CHAR] A [CHAR] F 1+ WITHIN IF [CHAR] 7 - THEN ;

: initline ( srcaddr bytecount linenum -- )
  16* CELLS grid +             \ srcaddr\bytecount\tgtaddr
  SWAP 0 DO                    \ srcaddr\tgtaddr
    OVER I + C@ char>digit DUP 16 < IF
      2^n                      \ srcaddr\tgtaddr\2^<digit>
      OVER !                   \ srcaddr\tgtaddr
      CELL+                    \ srcaddr\tgtaddr-next
      #unknown 1-!
    ELSE
      [CHAR] : <> IF CELL+ THEN
    THEN
  LOOP
  2DROP ;

: inits ( -- )
  0 #solution !
  256 #unknown !
  grid 256 0 DO
    $FFFF OVER !
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
 
  \ Original design.
  S" 0...:.5.7:.9.B:.DEF" 0  initline
  S" 45..:C..F:...2:..AB" 1  initline
  S" ..A.:..2.:.D..:.5.7" 2  initline
  S" C..F:8.A.:.5..:01.3" 3  initline

  S" 1.0.:7..4:D...:..C6" 4  initline
  S" .A..:.3.5:..4.:...9" 5  initline
  S" 6..8:..1.:72..:5..4" 6  initline
  S" ..9.:2..C:E3.8:..1." 7  initline

  S" 2..1:5..6:...C:...." 8  initline
  S" B..C:..D.:.8..:.F.5" 9  initline
  S" ....:.B.1:..0.:6..A" 10 initline
  S" 5...:..F.:...D:..0." 11 initline

  S" 3..0:B..A:.6.1:E..8" 12 initline
  S" 9.C.:..7.:30..:.A.1" 13 initline
  S" A.D.:..3.:.E..:.6.0" 14 initline
  S" .8..:E0..:..C.:D4.." 15 initline

  \ Transaction stack initialization.
  tstk-bottom tstkp !
  FALSE TO logtrans

  \ Statistical data initialization.
  0. ncb 2!
  0 #backtrack !
  0. #zgcv ! #cvio !           \ Initialize exception counts
  0. reclev ! reclevmax ! ;    \ and recursion level counts

\ -------------------------------------------------------------
\ Visualization.

\ Underline character rendition on.
: +ul ( -- )
  stopon1st 0= debug OR IF EXIT THEN
  #27 EMIT ." [4m" ;

\ Underline character rendition off.
: -ul ( -- )
  stopon1st 0= debug OR IF EXIT THEN
  #27 EMIT ." [m" ;

\ Turn off the cursor (VT200 control sequence).
: -cursor ( -- )
  stopon1st 0= debug OR IF EXIT THEN
  #27 EMIT ." [?25l" ;

\ Turn on the cursor (VT200 control sequence).
: +cursor ( -- )
  stopon1st 0= debug OR IF EXIT THEN
  #27 EMIT ." [?25h" ;

: mask>char ( mask -- char )
  DUP countbits                \ mask\nbits
  1 = IF
    16 0 DO
      DUP I 2^n = IF
        DROP I UNLOOP
        DUP 9 > IF  7 + THEN [CHAR] 0 +
        EXIT
      THEN
    LOOP
    1 ABORT" WTF?"             \ This should never be executed
  THEN
  DROP wildc ;

: display-grid ( -- )
  grid 16 0 DO                 \ J has the current row#
    16 0 DO                    \ I has the current col#
      DUP @ mask>char
        EMIT SPACE
      CELL+
    LOOP
    CR
  LOOP DROP ;

\ -------------------------------------------------------------
\ Four by four exclusion/filtering.

\ No side effects.
: 4x4-getmask ( xcol yrow -- mask | exception-triggered )
  0                            \ Sanity check
  $FFFF                        \ Initial mask
  \ xcol\yrow\check\mask
  4 0 DO                       \ J has dy
    4 0 DO                     \ I has dx
      3 PICK I +               \ Absolute col#
      3 PICK J + 16* +
      CELLS grid +
      @ DUP countbits 1 = IF
        \ xcol\yrow\check\mask\val
        ROT OVER  \ xcol\yrow\mask\val\check\val
        2DUP AND  \ xcol\yrow\mask\val\check\val\(check&val)

        IF                     \ Bit already set!!!
          #cvio 1+!
          cvio_exc THROW       \ Constraint violation detected
        THEN

        \ xcol\yrow\mask\val\check\val
        OR                  \ xcol\yrow\mask\val\(check|val)
        -rot                \ xcol\yrow\(check|val)\mask\val
        INVERT AND          \ xcol\yrow\(check|val)\(mask&~val)
      ELSE
        DROP
      THEN
    LOOP
  LOOP
  \ xcol\yrow\check\mask
  NIP NIP NIP ;

: 4x4-setmask ( xcol yrow mask -- | exception-triggered )
  \ If 'mask' is zero, it means that all cells in that 4x4
  \ quadrant are resolved (fixed points). Just exit should
  \ such a condition occur.
  ?DUP 0= IF 2DROP EXIT THEN

  -rot                         \ mask\xcol\yrow
  4 0 DO                       \ J has dy
    4 0 DO                     \ I has dx
      OVER I +                 \ Absolute col#
      OVER J + 16* +
      CELLS grid +             \ mask\xcol\yrow\saddr
      DUP @ DUP countbits 1 <> IF
        \ mask\xcol\yrow\saddr\sval
        4 PICK AND             \ mask\xcol\yrow\saddr\sval-new
        ?DUP IF
          SWAP update-spot
        ELSE
          #zgcv 1+!
          zgcv_exc THROW       \ Zero grid cell value detected
        THEN
      ELSE
        2DROP
      THEN
      \ mask\xcol\yrow
    LOOP
  LOOP
  DROP 2DROP ;

\ 4x4 block logic: either a spot is known or the list
\ of alternatives must exclude all known spots values.
: 4x4-reduce-allquads ( -- | exception-triggered )
  4 0 DO              \ Iterate over quadrant rows
    4 0 DO            \ Iterate over quadrant columns
      I 4 * J 4 *
      2DUP 4x4-getmask
      ( xcol#\yrow#\new-possibly-zero-mask ) 4x4-setmask
    LOOP
  LOOP ;

\ -------------------------------------------------------------
\ Horizontal exclusion/filtering.

\ ANS94 3.2.3.3 Return stack:
\ A program shall not access from within a DO-LOOP values
\ placed on the return stack before the loop was entered.
\ Note: this is enforced in SwiftForth but not in GForth.

\ No side effects.
: horiz-getmask ( yrow -- mask | exception-triggered )
  16* CELLS grid +             \ Start of row address
  0                            \ Sanity check
  $FFFF                        \ Initial mask
  16 0 DO                      \ Iterate over columns
    \ srow-addr\check\mask
    2 PICK I CELLS + @ DUP countbits 1 = IF
      \ srow-addr\check\mask\val
      ROT OVER \ srow-addr\mask\val\check\val
      2DUP AND \ srow-addr\mask\val\check\val\(check&val)

      IF                       \ Bit is already set!!!
        #cvio 1+!
        cvio_exc THROW         \ Constraint violation detected
      THEN

      \ srow-addr\mask\val\check\val
      OR                       \ srow-addr\mask\val\(check|val)
      -rot                     \ srow-addr\(check|val)\mask\val
      INVERT AND
    ELSE
      DROP
    THEN
  LOOP
  \ srow-addr\check\mask
  NIP NIP ;

: horiz-setmask ( yrow mask -- | exception-triggered )
  \ If 'mask' is zero. just return a success indication.
  ?DUP 0= IF DROP EXIT THEN

  SWAP
  16* CELLS grid +
  16 0 DO                      \ Iterate over columns
    DUP @ DUP countbits 1 <> IF
      \ mask\saddr\sval
      2 PICK AND               \ mask\saddr\sval-new
      ?DUP IF
        OVER update-spot
      ELSE
        #zgcv 1+!
        zgcv_exc THROW         \ Zero grid cell value detected
      THEN
    ELSE
      DROP
    THEN
    \ mask\saddr
    CELL+
  LOOP
  2DROP ; 

\ -------------------------------------------------------------
\ Vertical exclusion/filtering.

\ No side effects.
: vert-getmask ( xcol -- mask | exception-triggered )
  CELLS grid +                 \ Start of column address
  0                            \ Sanity check
  $FFFF                        \ Initial mask
  16 0 DO                      \ Iterate over rows
    \ scol-addr\check\mask
    2 PICK I 16* CELLS + @ DUP countbits 1 = IF
      \ scol-addr\check\mask\val
      ROT OVER \ scol-addr\mask\val\check\val
      2DUP AND \ scol-addr\mask\val\check\val\(check&val)

      IF                       \ Bit is already set!!!
        #cvio 1+!
        cvio_exc THROW         \ Constraint violation detected
      THEN

      \ scol-addr\mask\val\check\val
      OR                       \ scol-addr\mask\val\(check|val)
      -rot                     \ scol-addr\(check|val)\mask\val
      INVERT AND
    ELSE
      DROP
    THEN
  LOOP
  \ srow-addr\check\mask
  NIP NIP ;

: vert-setmask ( xcol mask -- | exception-triggered )
  \ If 'mask' is zero. just return a success indication.
  ?DUP 0= IF DROP EXIT THEN

  SWAP
  CELLS grid +                 \ Beginning of column address
  16 0 DO                      \ Iterate over rows
    DUP @ DUP countbits 1 <> IF
      \ mask\saddr\sval
      2 PICK AND               \ mask\saddr\sval-new
      ?DUP IF
        OVER update-spot       \ mask\saddr
      ELSE
        #zgcv 1+!
        zgcv_exc THROW         \ Zero grid cell value detected
      THEN
    ELSE
      DROP
    THEN
    \ mask\saddr
    16 CELLS +
  LOOP
  2DROP ;

\ We do not not have to check for inconsistencies at all.
\ They will result in exceptions being raised by 'update-spot'.
: reduceall ( -- | exception-triggered )
  4x4-reduce-allquads

  16 0 DO
    I DUP horiz-getmask horiz-setmask
    I DUP vert-getmask  vert-setmask
  LOOP ;

\ -------------------------------------------------------------
\ Primary way of altering a grid's spot but not the only one!
\ 'speculate' does unregistered grid changes as well.
\ The only changes we can see here are inferred. Undo
\ operations are carried out via 'tstk-pop'.

: _update-spot ( val saddr -- | exception-triggered )
  assert-valid-grid-addr

  DUP @ countbits 1 = IF
    CR ." _update-spot: attempt to modify a fixed point at: "
    h. ABORT
  THEN

  2DUP @ = IF                  \ Value not changed
    2DROP EXIT
  THEN

  logtrans IF                  \ Transaction is logged
    FALSE OVER tstk-push
  THEN

  \ This update resolves the spot pointed to by 'saddr'.
  OVER countbits 1 = IF #unknown 1-! THEN

  \ Commit this change to the grid.
  |visual 2DUP !               \ val\saddr
  NIP                          \ saddr

  \ Do not validate constraints until we are speculating.
  logtrans 0= IF DROP EXIT THEN

  \ The change under consideration remains probatory.
  \ Check for possible inconsistencies at 'saddr'.
  getxy-from-grid-addr 2DUP    \ xcol\yrow\xcol\yrow

  \ 4x4 constraint verification.
  $C AND SWAP $C AND SWAP      \ Mask out bits 2-0 of col#/row#
  2DUP 4x4-getmask 4x4-setmask

  \ Horizontal constraint verification ( S: xcol\yrow ).
  DUP horiz-getmask horiz-setmask

  \ Vertical constraint verification ( S: xcol ).
  DUP vert-getmask vert-setmask

  ;                            \ --

' _update-spot IS update-spot  \ Can't do that in 'inits'

\ -------------------------------------------------------------
\ Speculation.

: infer ( -- success-flag )
  256                          \ '#unknown' worst case scenario
  BEGIN
    ['] reduceall CATCH        \ unkmax\exc# | unkmax\0
    DUP 0= OVER zgcv_exc = OR OVER cvio_exc = OR 0= IF
      \ The exception caught is not one of ours.
      CR ." infer: caught exception " . ABORT
    THEN
    IF DROP FALSE EXIT THEN    \ Exception occurred
    #unknown @ >
  WHILE
    #unknown @
  REPEAT
  TRUE ;

\ "[Gordon Gekko]: The point is ladies and gentlemen that
\ greed, for lack of a better word, is good." from the "Wall
\ Street" movie, 1987.
: get-unresolved ( -- grid-cell-addr | FALSE )
  grid DUP @ countbits          \ minp\minp@#bits
  OVER CELL+                    \ minp\minp@#bits\curp

  255 0 DO
    DUP @ countbits           \ minp\minp@#bits\curp\curp@#bits

    \ The newly selected minimum bit count cannot ever be 1.
    DUP 1 = IF
      DROP
    ELSE
      \ minp@#bits can be 1, indicating a resolved spot.
      \ If it is, accept anything but 1 as a new minimum.
      2 PICK 1 = IF           \ minp\minp@#bits\curp\curp@#bits
        2nip 2DUP
      THEN

      \ minp\minp@#bits\curp\curp@#bits
      DUP 2 = IF               \ 2 as a good enough minimum
        2nip OVER LEAVE        \ curp\curp@#bits\curp
      THEN

      DUP 3 PICK < IF         \ minp\minp@#bits\curp\curp@#bits
        2nip OVER              \ curp\curp@#bits\curp
      ELSE
        DROP
      THEN
    THEN

    CELL+                      \ minp\minp@#bits\curp
  LOOP
  DROP                         \ minp\minp@#bits

  \ If the minimum bit count is 1 the problem is solved.
  1 = IF DROP FALSE THEN ;

\ Increment recursion level counter and maintain the maximum.
: rl+ ( -- ) reclev 1+!
  reclev @ reclevmax @ MAX reclevmax ! ;

\ Decrement recursion level counter.
: rl- ( -- ) reclev 1-! ;

: ingest-digest ( target-addr -- )
  sha1.h0 @ OVER ! CELL+
  sha1.h1 @ OVER ! CELL+
  sha1.h2 @ OVER ! CELL+
  sha1.h3 @ OVER ! CELL+
  sha1.h4 @ SWAP ! ;

: emergency-exit ( ... -- )
  \ Drain the data stack.
  BEGIN DEPTH WHILE DROP REPEAT
\ wasteit
  CR QUIT ;                    \ Clear the return stack

: check-for-new-solution ( -- )
  \ If #solution@ is zero, compute grid SHA1 digest, store
  \ it to sol-digest0 (5 CELLS), increment #solution@ and
  \ return.
  #solution @ 0= IF
    grid app.msgbuf 256 CELLS MOVE \ Need to copy the data in
    256 CELLS app.msglen !
    sha1.digest
    sol-digest0 ingest-digest
    #solution 1+!
    stopon1st 0= IF
      CR display-grid          \ Debug information
    THEN
    EXIT
  THEN

  \ Otherwise, compute grid SHA1 digest, store it to
  \ sol-digest1, compare that to sol-digest0 and if different:
  \ increment #solution@.
  \ SHA1 encoding restrictions apply: up to 512 CELLS of data.
  grid app.msgbuf 256 CELLS MOVE \ Need to copy the data in
  256 CELLS app.msglen !
  sha1.digest
  sol-digest1 ingest-digest

  sol-digest0 5 CELLS sol-digest1 OVER COMPARE 0= IF
    EXIT                       \ Duplicate detected
  THEN
  
  #solution 1+!
  stopon1st 0= IF
    CR display-grid            \ Debug information
  THEN

  #solution @ 2 = IF
    CR ." More than one solution found"
    emergency-exit
  THEN ;

: speculate ( -- success-flag )
  rl+                          \ Increment recursion level

\ reclev @ 11 > IF emergency-exit THEN

  get-unresolved               \ Look for an unresolved spot
  DUP 0= IF                    \ Problem solved
    check-for-new-solution
    INVERT
    EXIT
  THEN

  DUP @                        \ saddr\sval

  debug IF
    CR ." >speculate at rl " reclev ?
    ." mask: " DUP h.
    debug 2 AND IF 0 sdigest THEN
  THEN

  \ The list of set bits in TOS indicate the possibilities
  \ for the selected spot. Explore these alternatives.
  16 0 DO
    DUP I 2^n DUP >R AND IF
      TRUE 2 PICK tstk-push    \ Insert transaction boundary

      R> 2 PICK
        +ul |visual -ul
        #unknown 1-!           \ Spot provisionally resolved
        !                      \ Un-logged update-spot

      debug IF
        CR reclev @ SPACES ." >infer at rl " reclev ?
        debug 2 AND IF 0 sdigest THEN
        debug 8 AND IF
IFNVF     ." I/I': " I . I' .  \ VFX does not have I'
IFVF      ." I: " I .
        THEN
        debug 4 AND IF
          ." #cvio " #cvio ? ." #zgcv " #zgcv ?
        THEN
      THEN
      infer
      debug IF
        CR reclev @ SPACES ." <infer at rl " reclev ?
        debug 2 AND IF 1 sdigest THEN
        debug 8 AND IF
IFNVF     ." I/I': " I . I' .  \ VFX does not have I'
IFVF      ." I: " I .
        THEN
        debug 4 AND IF
          ." #cvio " #cvio ? ." #zgcv " #zgcv ?
        THEN
      THEN

      IF                       \ No inconsistencies detected
        RECURSE IF
          stopon1st IF
            debug IF
              CR ." <speculate at rl " reclev ?
              debug 2 AND IF 0 sdigest THEN
            THEN
            #solution 1+!
            2DROP UNLOOP TRUE EXIT
          ELSE
            \ Possible solution found, make sure it's not a dup
            check-for-new-solution
          THEN
        THEN
      THEN

      debug IF
        CR reclev @ SPACES ." >backtrack at rl " reclev ?
        debug 2 AND IF 0 sdigest THEN
      THEN

      \ Backtrack up to the last transaction boundary.
      BEGIN tstk-pop UNTIL
      #backtrack 1+!           \ Increment #backtrack

      debug IF
        CR reclev @ SPACES ." <backtrack at rl " reclev ?
        debug 2 AND IF 0 sdigest THEN
      THEN
    ELSE
      R> DROP
    THEN
  LOOP

  debug IF
    CR ." <speculate at rl " reclev ?
    ." mask: " DUP h.
    debug 2 AND IF 0 sdigest THEN
  THEN

  2DROP

  FALSE                        \ Dead end reached
  rl- ;                        \ Decrement recursion level

: micros-elapsed ( -- microseconds )
  \ Starting timestamp
  IFGF utime
  IFSF get-time
  IFVF ticks

  speculate DROP

  \ Ending timestamp
  IFGF utime 2SWAP DNEGATE D+ DROP
  IFSF get-time ROT - 1000000 * SWAP ROT - +
  IFVF ticks SWAP - 1000 *
  ;

: main ( -- )
  inits

  stopon1st debug 0= AND IF
    PAGE -cursor display-grid
  THEN

  infer 0= IF
    +cursor
    CR ." No solutions"
    emergency-exit
  THEN

  \ From here on, everything that could be inferred is in.
  TRUE TO logtrans

  stopon1st IF
    debug 0= IF PAGE display-grid THEN
    micros-elapsed
    debug 0= IF 31 15 AT-XY THEN

    CR ." Maximum recursion level: " reclevmax ?
    CR ." Problem solved at level: " reclev ?
    CR ." 'countbits' called " ncb 2@ <# #S #> TYPE ."  times"
    CR ." Backtracked " #backtrack ? ." times"
    +cursor
  ELSE
    micros-elapsed
    CR #solution ? ." solution(s) found"
    CR ." 'countbits' called " ncb 2@ <# #S #> TYPE ."  times"
    CR ." Backtracked " #backtrack ? ." times"
  THEN

  CR #cvio ? ." constraint violations"
  CR #zgcv ? ." zero grid cell values"
  CR . ." us elapsed" ;

main 7 EMIT

