\ SHA-1 sample code for GNU Forth 0.7.3 or SwiftForth 3.7.9
\ Either a 64 or 32 bit cell size is assumed.
\
\ References:
\ https://www.rfc-editor.org/rfc/rfc3174
\ https://en.wikipedia.org/wiki/SHA-1
\
\ Note: FOB is a TLA for "First Order of Business."

DECIMAL

\ The 64 bit question comes up primarily with respect to
\ SwiftForth and its upcoming 4.0 flavor (a beta at the time of
\ this writing). However, there are also 32 bit GForth flavors.
: IF64 [ 1 CELLS 8 <> ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFN64 [ 1 CELLS 8 = ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE

\ Assert basic assumptions.
1 CELLS 8 = CONSTANT sha1.is64
1 CELLS 4 = CONSTANT sha1.is32

sha1.is64 sha1.is32 OR 0= [IF]
  ." Unsupported cell size" ABORT
[THEN]

VARIABLE sha1.is-little-endian  1 sha1.is-little-endian !

VARIABLE sha1.h0   VARIABLE sha1.a
VARIABLE sha1.h1   VARIABLE sha1.b
VARIABLE sha1.h2   VARIABLE sha1.c
VARIABLE sha1.h3   VARIABLE sha1.d
VARIABLE sha1.h4   VARIABLE sha1.e

\ Application supplied data to be digested the SHA-1 way.
CREATE   app.msgbuf 512 CELLS ALLOT
VARIABLE app.msglen            \ byte count
VARIABLE app.msgptr            \ current encoding position

\ Intrinsic SHA-1 data, i.e. sizes are not negotiable!
CREATE   sha1.encbuf 64 ALLOT  \ 512/8
CREATE   sha1.w 320 ALLOT      \ 80 32 bit words
VARIABLE sha1.total-bytecount  \ cumulative user data size
VARIABLE sha1.perblock-bytecount

\ We need state information. 'sha1.digest-one-block' will be
\ invoked as many times as needed and yet we also need to have
\ the trailing $80 terminator and the message length (in bits)
\ expressed as an MSB first u64 value.
VARIABLE sha1.state            \ One of the following values
0 CONSTANT sha1.state-started
1 CONSTANT sha1.state-terminated
2 CONSTANT sha1.state-completed

\ -------------------------------------------------------------
\ 64 bit code.

1 CELLS 8 = [IF]
\ Regular addition modulo 2^32 on a 64 bit platform.
: sha1.+:32 ( u32a u32b -- u32c ) + $FFFFFFFF AND ;

: sha1.><:64 ( u1 -- u2 )
[ sha1.is-little-endian C@ ] [IF]
  >R
  R@                       56 LSHIFT      \ byte 0 to byte 7
  R@ $FF00             AND 40 LSHIFT OR   \ byte 1 to byte 6
  R@ $FF0000           AND 24 LSHIFT OR   \ byte 2 to byte 5
  R@ $FF000000         AND  8 LSHIFT OR   \ byte 3 to byte 4
  R@ $FF00000000       AND  8 RSHIFT OR   \ byte 4 to byte 3
  R@ $FF0000000000     AND 24 RSHIFT OR   \ byte 5 to byte 2
  R@ $FF000000000000   AND 40 RSHIFT OR   \ byte 6 to byte 1
  R> $FF00000000000000 AND 56 RSHIFT OR ; \ byte 7 to byte 0
[ELSE]
  ;
[THEN]

: sha1.store.bitcount ( msg.bytecount 8 -- )
  * 
    sha1.><:64                 \ Message bitcount to big endian
    56 sha1.encbuf + ! ;

[THEN]                         \ 64 bit code

\ -------------------------------------------------------------
\ 32 bit code.

1 CELLS 4 = [IF]
\ Regular addition modulo 2^32 on a 32 bit platform.
: sha1.+:32 + ;

: sha1.><:32 ( u1 -- u2 )
[ sha1.is-little-endian C@ ] [IF]
  >R                           \ S: R: u1
  R@             $18 RSHIFT    \ u1:byte3 to u2:byte0
  R@ $FF0000 AND   8 RSHIFT OR \ u1:byte2 to u2:byte1
  R@ $FF00   AND   8 LSHIFT OR \ u1:byte1 to u2:byte2
  R> $FF     AND $18 LSHIFT OR \ u1:byte0 to u2:byte3
  ( S: u2 R : ) ;
[ELSE]
  ;
[THEN]

: sha1.store.bitcount ( msg.bytecount 8 -- )
  UM*
    sha1.><:32 56 sha1.encbuf + !   \ Most significant cell
    sha1.><:32 60 sha1.encbuf + ! ; \ Least significant cell

[THEN]                         \ 32 bit code

\ -------------------------------------------------------------
\ Acquire a 32 bit value stored in big endian byte order.
\ That value resides at byte offset 'index' times 4 from
\ the base fixed size buffer 'sha1.w'.
: sha1.getword:32 ( index -- 32bitvalue )
  4 * sha1.w +                 \ Pointing to byte 3
  DUP C@ $18 LSHIFT        SWAP 1+ \ Pointing to byte 2
  DUP C@ $10 LSHIFT ROT OR SWAP 1+ \ Pointing to byte 1
  DUP C@ 8   LSHIFT ROT OR SWAP 1+ \ Pointing to byte 0
  C@ OR ;

\ Store '32bitvalue' in big endian byte order to the 'sha1.w'
\ array. The first byte affected resides at byte offset 'index'
\ times 4 from the base fixed size buffer 'sha1.w'.
: sha1.putword:32 ( 32bitvalue index -- )
  4 * sha1.w +                 \ Pointing to byte 3
  OVER             $18 RSHIFT OVER C! 1+
  OVER $FF0000 AND $10 RSHIFT OVER C! 1+
  OVER $FF00   AND 8   RSHIFT OVER C! 1+
  SWAP $FF     AND
  SWAP C! ;

\ -------------------------------------------------------------

: sha1.initvars ( -- )
  $67452301 sha1.h0 !
  $EFCDAB89 sha1.h1 !
  $98BADCFE sha1.h2 !
  $10325476 sha1.h3 !
  $C3D2E1F0 sha1.h4 !
  sha1.state-started sha1.state !
  0 sha1.total-bytecount !

  \ We do surrender usage of app.msgptr to the SHA1 code.
  app.msgbuf app.msgptr ! ;

\ -------------------------------------------------------------
\ Rotate '32bitvalue' to the left 'count' times.

: sha1.leftrotate:32 ( 32bitvalue count )
  DUP $1F > IF                 \ Deal with ambiguous condition
    2DROP 0 EXIT
  THEN

  2DUP                      \ 32bitvalue\count\32bitvalue\count
  LSHIFT
  IF64 $FFFFFFFF AND       \ 32bitvalue\count\32bitvalue<<count
  -rot                     \ 32bitvalue<<count\32bitvalue\count
  32 SWAP -
  RSHIFT             \ 32bitvalue<<count\32bitvalue<<(32-count)
  IF64 $FFFFFFFF AND
  OR ;

\ -------------------------------------------------------------

: sha1.expand-block ( -- )
  sha1.encbuf sha1.w 64 CMOVE  \ Current block to 'sha1.w'

  \ Extend the sixteen 32-bit words into eighty 32-bit words
  80 16 DO
    i 3  - sha1.getword:32
    i 8  - sha1.getword:32 XOR
    i 14 - sha1.getword:32 XOR
    i 16 - sha1.getword:32 XOR
    1 sha1.leftrotate:32
    i sha1.putword:32
  LOOP ;

\ -------------------------------------------------------------

: sha1.digest-one-block ( -- )
  sha1.expand-block

  \ Per block hash value initialization.
  sha1.h0 @ sha1.a !
  sha1.h1 @ sha1.b !
  sha1.h2 @ sha1.c !
  sha1.h3 @ sha1.d !
  sha1.h4 @ sha1.e !

  \ Main loop
  80 0 DO
    I 0 20 WITHIN IF
      $5A827999
      sha1.b @ sha1.c @ AND sha1.b @ INVERT sha1.d @ AND OR
    THEN

    I 20 40 WITHIN IF
      $6ED9EBA1
      sha1.b @ sha1.c @ XOR sha1.d @ XOR
    THEN

    I 40 60 WITHIN IF
      $8F1BBCDC
      sha1.b @ sha1.c @ AND
        sha1.b @ sha1.d @ AND OR
        sha1.c @ sha1.d @ AND OR
    THEN

    I 60 80 WITHIN IF
      $CA62C1D6
      sha1.b @ sha1.c @ XOR sha1.d @ XOR
    THEN

    \ S: sha1-k\sha1-f

    sha1.+:32
      sha1.a @ 5 sha1.leftrotate:32 sha1.+:32
      sha1.e @ sha1.+:32
      i sha1.getword:32 sha1.+:32 \ aka sha1-temp
    sha1.d @ sha1.e !
    sha1.c @ sha1.d !
    sha1.b @ 30 sha1.leftrotate:32 sha1.c !
    sha1.a @ sha1.b !
    sha1.a !                   \ sha1-a = sha1-temp
  LOOP

  sha1.a @ sha1.h0 @ sha1.+:32 sha1.h0 !
  sha1.b @ sha1.h1 @ sha1.+:32 sha1.h1 !
  sha1.c @ sha1.h2 @ sha1.+:32 sha1.h2 !
  sha1.d @ sha1.h3 @ sha1.+:32 sha1.h3 !
  sha1.e @ sha1.h4 @ sha1.+:32 sha1.h4 ! ;

\ -------------------------------------------------------------
\ This is the tricky part of the encoding algorithm. It handles
\ user data to SHA1 data specific transfers. It does so with
\ the help of a state variable so that, ultimately, we meet
\ the requirements stated in FIPS PUB 180-1.
\ That covers the message terminator and the actual user data
\ bit count expressed as a 64 bit unsigned value (MSB first).
\
\ This routine takes care of:
\
\ - transferring user data from app.msgbuf (app.msgptr and
\   app.msglen are used as input parameters) to sha1.encbuf.
\   We own app.msgptr but nothing else beyond that.
\ - padding sha1.encbuf in a canonical (MSB first) manner.
\ - returning a non-completion indication.

: sha1.refill-encbuf ( -- moretogo-flag )
  sha1.state @ sha1.state-completed = IF FALSE EXIT THEN

  0 sha1.perblock-bytecount !  \ No user data encoded so far
  sha1.encbuf 64 ERASE         \ FOB: erase the encoding buffer

  \ Any more user data to be processed?
  app.msgbuf app.msglen @ + app.msgptr @ <> IF           \ Yes!
    \ Figure out how many bytes of user data we can handle now.
    app.msgptr @ app.msgbuf -  \ S: already-encoded-bytecount
    app.msglen @ SWAP -        \ S: byte-count-remaining
    \ We can accomodate up to 64 bytes per block.
    64 MIN                     \ S: this-time-bytecount
    sha1.perblock-bytecount !

    \ Transfer what we can handle right now to sha1.encbuf
    app.msgptr @ sha1.encbuf sha1.perblock-bytecount @ CMOVE

    \ Update app.msgptr accordingly.
    sha1.perblock-bytecount @ DUP app.msgptr +!
    \ And the total user data byte count while we're at it.
      sha1.total-bytecount +!
  THEN

  \ Did we account for all of the user data so far?
  sha1.total-bytecount @ app.msglen @ =
  \ and are we still to emit the message terminator?
  sha1.state @ sha1.state-terminated <> AND IF
    \ Can we emit the terminator in the current block?
    sha1.perblock-bytecount @ 64 < IF                    \ Yes!
      sha1.perblock-bytecount @ sha1.encbuf +
        $80 SWAP C!            \ Insert the terminator
      1 sha1.perblock-bytecount +!
      sha1.state-terminated sha1.state ! \ Update SHA1 state
    THEN
  THEN

  \ At this point we have a useful 'sha1.encbuf' which may or
  \ may not include the required terminator bit. We might still
  \ be able to squeeze in the message (uncounted) u64 bitcount
  \ parameter but only if we already are in the
  \ 'sha1.state-terminated' state. Otherwise just pass the
  \ buck on...
  sha1.state @ sha1.state-terminated <> IF
    TRUE EXIT                  \ Please do call us again!
  THEN

  \ We already emitted the terminator. Can we fit the message's
  \ length bitcount (u64) into the current 'sha1.encbuf'? The
  \ message's bitcount length is inserted in an atomic manner--
  \ not across 512 bit blocks.
  sha1.perblock-bytecount @ 56 < IF \ 56 as in 64 - 8
    app.msglen @ sha1.total-bytecount @ <> ABORT" WTH?"
    app.msglen @ 8 sha1.store.bitcount
    sha1.state-completed sha1.state ! \ Update SHA1 state
  THEN  
  TRUE ;                       \ Please do call us again!

\ -------------------------------------------------------------

: sha1.digest ( -- )
  sha1.initvars

  BEGIN
    sha1.refill-encbuf
  WHILE
    sha1.digest-one-block
  REPEAT ;

: .sha1.digest ( -- )
  sha1.digest

  BASE @ >R HEX
  sha1.h0 @ S>D <# # # # # # # # # #>               TYPE
  sha1.h1 @ S>D <# # # # # # # # # [CHAR] : HOLD #> TYPE
  sha1.h2 @ S>D <# # # # # # # # # [CHAR] : HOLD #> TYPE
  sha1.h3 @ S>D <# # # # # # # # # [CHAR] : HOLD #> TYPE
  sha1.h4 @ S>D <# # # # # # # # # [CHAR] : HOLD #> TYPE
  R> BASE ! ;

\ -------------------------------------------------------------
\ Conceptually we have three different entities:
\
\ - the input message itself, which can be anything of size
\   strictly less than 2^64-8 bits long.
\ - a copy of the input message stored in a fixed size buffer.
\   This is app.msgbuf, app.msgptr and app.msglen (in bytes).
\ - the current 512 bit block being operated on by
\   sha1.digest-one-block.

: sdigest ( i*x skip-cell-count -- i*x )
  0 app.msglen !               \ expressed in bytes
  app.msgbuf app.msgptr !

  >R
  DEPTH R@ ?DO
    I PICK  app.msgptr @ !
    1 CELLS app.msgptr +!
    1 CELLS app.msglen +!
  LOOP
  R> DROP

  .sha1.digest ;

\ -------------------------------------------------------------
\ Tests cases as defined in RFC 3174 (at the end of the C code).

FALSE [IF]

: target-status ( -- )
  CR ." Target is "
  sha1.is64 IF S" 64" ELSE S" 32" THEN
  TYPE ."  bit "
  sha1.is-little-endian C@ IF S" little" ELSE S" big" THEN
  TYPE ."  endian." ;

: digest-sliteral ( addr bytecount -- )
  DUP app.msglen ! app.msgbuf SWAP CMOVE
  app.msgbuf app.msgptr !
  .sha1.digest ;

target-status

S" abc" CR digest-sliteral
\ Expected output is:
\ A9993E36:4706816A:BA3E2571:7850C26C:9CD0D89D

S" abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
  CR digest-sliteral
\ Expected output is:
\ 84983E44:1C3BD26E:BAAE4AA1:F95129E5:E54670F1

\ RFC 3174 tests that have a repeat count > 1 are not supported.

\ Tests from the SHA-1 wikipedia page.
S" The quick brown fox jumps over the lazy dog"
  CR digest-sliteral
\ Expected output is:
\ 2FD4E1C6:7A2D28FC:ED849EE1:BB76E739:1B93EB12

S" The quick brown fox jumps over the lazy cog"
  CR digest-sliteral
\ Expected output is:
\ DE9F2C7F:D25E1B3A:FAD3E85A:0BD17D9B:100DB4B3

\ More tests from https://www.di-mgt.com.au/sha_testvectors.html
S" " CR digest-sliteral
\ Expected output is:
\ DA39A3EE:5E6B4B0D:3255BFEF:95601890:AFD80709

S" abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
  CR digest-sliteral
\ Expected output is:
\ A49B2446:A02C645B:F419F995:B6709125:3A04A259

[THEN]

