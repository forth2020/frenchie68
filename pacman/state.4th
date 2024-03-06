: find79                       \ -- xt|0; find79 <name>
  BL WORD
  DUP C@ 0= IF DROP ." Missing word name" EXIT THEN
  FIND 0= IF DROP FALSE THEN ;

: gf? [ find79 utime ] LITERAL ;      \ TRUE if GNU Forth
: z7? [ find79 mcc ] LITERAL ;        \ TRUE if Z79Forth/A

: IFGF [ gf? 0= ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFZ7 [ z7? 0= ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE

IFZ7 : 2VARIABLE VARIABLE 1 CELLS ALLOT ;
IFZ7 : D>S DROP ;

VARIABLE _case
: case! _case ! ;
: case@ _case @ ;
: case? case@ = ;

\ -------------------------------------------------------------
\ Euclidian distance calculation support code.

\ <= is non-standard!!!
\ However GNU Forth, SwiftForth, VFX and Z79Forth support it.
\ : <= ( a b -- flag )
\   2DUP < ROT ROT = OR ;

\ Integer square root calculation. See wikipedia.org,
\ integer_square_root (binary search).
\ Note: this will not converge for negative values of y!!!
: isqrt ( y -- x )
  >R
  0 R@ 1+           \ S: L\R
  BEGIN
    2DUP 1- <>
  WHILE             \ S: L\R
    2DUP + 1 RSHIFT \ S: L\R\M
    DUP DUP *       \ S: L\R\M\M^2
    R@ <= IF        \ S: L\R\M
      ROT DROP SWAP \ S: M\R
    ELSE
      NIP           \ S: L\M
    THEN
  REPEAT
  DROP R> DROP ;

\ -------------------------------------------------------------
\ Ghost mode logic follows.

0 CONSTANT mode_scatter
1 CONSTANT mode_chase \ Each ghost may defines its own policy!
2 CONSTANT mode_fright
3 CONSTANT mode_unspec

200 CONSTANT clkperiod \ Expressed in milliseconds
120 CONSTANT super-clkcycles

\ Those are global variables (in disguise).
mode_scatter VALUE gm_cur
mode_unspec  VALUE gm_prv

IFGF 2VARIABLE utime0
2VARIABLE gamlev

0    VALUE gm_seqno
TRUE VALUE gm_timer_en
VARIABLE gm_timer
VARIABLE fright_timer      \ Normally PM.issuper

\ The ghost mode scheduling table.
CREATE gm_sched
\           L1      L2-4    L5+     seqno
( Scatter ) 35 ,    35 ,    25 ,    \ 0
( Chase   ) 100 ,   100 ,   100 ,   \ 1
( Scatter ) 35 ,    35 ,    25 ,    \ 2
( Chase   ) 100 ,   100 ,   100 ,   \ 3
( Scatter ) 25 ,    25 ,    25 ,    \ 4
( Chase   ) 100 ,   5165 ,  5185 ,  \ 5
( Scatter ) 25 ,    1 ,     1 ,     \ 6
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
  + CELLS gm_sched + @ ;

\ XXX: Should be a ghost attribute
FALSE VALUE reversal_flag

: gm_seqno-getnext ( -- gm_seqno-next )
  gm_seqno DUP 6 < IF 1+ EXIT THEN
  DROP 7 ;          \ The sequence number is capped at 7

\ Called after a context change (sequence number or game level)
: gm-getnext ( -- mode )
  gamlev 2@ D>S gm_seqno gm_timer-initval-get
  DUP -1 <> DUP TO gm_timer_en IF
    gm_timer !
    gm_seqno 1 AND 0= IF
      mode_scatter
    ELSE
      mode_chase
    THEN 
  ELSE
    DROP mode_chase 
  THEN ;

\ Level entry initializations.
: le-inits ( -- )
IFGF utime utime0 2!
  0 fright_timer !
  0 TO gm_seqno
  gm-getnext  TO gm_cur
  mode_unspec TO gm_prv ;

: gm_prv-update ( mode -- )
  gm_cur mode_fright = IF EXIT THEN
  gm_cur TO gm_prv ;

: .mode ( mode -- )
  case!
  mode_scatter case? IF ." SCATTER" EXIT THEN
  mode_chase   case? IF ." CHASE  " EXIT THEN
  mode_fright  case? IF ." FRIGHT " EXIT THEN
  ." UNSPEC " ;

: .sitrep ( -- )
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
    ." gmt: " gm_timer @  4 .R SPACE
    ." rvd: " reversal_flag 2 .R

  \ Clear the reversal flag--all ghost instances.
  FALSE TO reversal_flag ;

\ This should be called only after le-inits in any given level.
: gm-switchto ( mode -- )
  DUP gm_cur = IF   \ Current mode is not changing
    DROP EXIT
  THEN

  \ The following, if TRUE, should be signalled to
  \ all ghost instances.
  gm_cur mode_fright <> TO reversal_flag

  gm_prv-update
  TO gm_cur ;

: super-enter ( -- )
  \ We might want to EXIT immediately depending on 'gamlev'
  gm_cur mode_fright = IF \ Already frightened
    super-clkcycles fright_timer ! \ Be kind, reset the timer!
    EXIT
  THEN

  gm_prv-update
  mode_fright TO gm_cur
  FALSE TO gm_timer_en             \ Suspend gm_timer
  super-clkcycles fright_timer ! ; \ Enable the 'fright' timer

: super-leave ( -- )
  gm_prv gm-switchto
  TRUE TO gm_timer_en ;            \ Re-enable gm_timer

: game-inits ( -- )
  1. gamlev 2! ;

: main ( -- )
  game-inits
  le-inits .sitrep
  BEGIN
    \ Need to poll for keyboard input:
    \ 'f' -> enter frightened mode.
    \ 'n' -> switch to the next game level.
    KEY? IF
      KEY case!
      [CHAR] f CASE? IF super-enter .sitrep THEN
      [CHAR] n CASE? IF
        gamlev 2@ 1. D+ gamlev 2!
        le-inits .sitrep
      THEN
    THEN

    gm_cur mode_fright = IF
      fright_timer @ ?DUP IF    \ Continue w/ frightened ghosts
        1- fright_timer !
      ELSE
        super-leave .sitrep
      THEN
    THEN

    gm_timer_en IF
      gm_timer @ ?DUP IF
        1- gm_timer !           \ Ghost mode unchanged
      ELSE
        gm_seqno-getnext TO gm_seqno
        gm-getnext gm-switchto  \ Re-compute gm parameters
        .sitrep
      THEN
    THEN

    clkperiod MS

  AGAIN ;

main

\ Test vectors:
\ game-inits le-inits .sitrep
\ mode_fright gm-switchto .sitrep \ fright from scatter
\ mode_fright gm-switchto .sitrep \ fright from fright
\ Following transition is conceivable but not realistic!
\ mode_chase  gm-switchto .sitrep \ chase  from fright
\ mode_fright gm-switchto .sitrep \ fright from chase
\ mode_chase  gm-switchto .sitrep \ chase  from fright

