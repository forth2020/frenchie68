\ SHA-1 sample code for Z79Forth/A. A 16 bit cell is assumed.
\ So is a big endian system as well as ANS94 Core
\ compatibility.
\
\ References:
\ https://www.rfc-editor.org/rfc/rfc3174
\ https://en.wikipedia.org/wiki/SHA-1
\
\ Glossary:
\ FOB is a TLA for "First Order of Business."
\ MSC means most significant cell.
\ LSC means least significant cell.
\
\ "Confidence is what you have before you understand the
\ problem." Woody Allen.

DECIMAL

: find79                       \ -- xt|0; find79 <name>
  BL WORD
  DUP C@ 0= IF DROP ." Missing word name" EXIT THEN
  FIND 0= IF DROP FALSE THEN ;

: z7? [ find79 MCC 1 CELLS 2 = AND ] LITERAL ;
: IFNZ7 [ z7? 0= ] LITERAL IF ABORT" Not supported!" THEN ;

\ Assert basic assumptions.
IFNZ7

: 2VARIABLE CREATE 2 CELLS ALLOT ;

2VARIABLE sha1.h0   2VARIABLE sha1.a
2VARIABLE sha1.h1   2VARIABLE sha1.b
2VARIABLE sha1.h2   2VARIABLE sha1.c
2VARIABLE sha1.h3   2VARIABLE sha1.d
2VARIABLE sha1.h4   2VARIABLE sha1.e

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
\ Define basic double primitives.

: 2xor ( ud1 ud2 -- ud3 )
  ROT XOR                      \ Handle the MSC
  -rot XOR SWAP ;              \ and then the LSC

: 2and ( ud1 ud2 -- ud3 )
  ROT AND                      \ Handle the MSC
  -rot AND SWAP ;              \ and then the LSC

: 2or ( ud1 ud2 -- ud3 )
  ROT OR                       \ Handle the MSC
  -rot OR SWAP ;               \ and then the LSC

: 2invert ( ud1 -- ud2 )
  SWAP INVERT                  \ Handle the LSC
  SWAP INVERT ;                \ and then the MSC

: .double ( ud1 -- ud1 )
  2DUP
  BASE @ >R
  2 BASE !
  <# # # # # # # # # # # # # # # # #
     # # # # # # # # # # # # # # # # #> TYPE
  R> BASE ! ;

: 2lshift ( ud1.l ud1.m ucount -- ud2.l ud2.m )
  \ 'ucount' must be in [0..31]
  DUP 0 32 WITHIN 0= ABORT" 2lshift: assertion failure"

  ?DUP 0= IF EXIT THEN         \ No change if ucount is 0
  >R                           \ ud1.l\ud1.m, R: ucount

  R@ 17 < IF
    \ Compute overflow bits from ud1.l
    OVER 16 R@ - RSHIFT        \ ud1.l\ud1.m\ud1.l>>(16-ucount)

    SWAP R@ LSHIFT OR
    SWAP R> LSHIFT
  ELSE
    R> 16 - RECURSE
    \ Simplified 16 2lshift: ( MSC <= LSC, LSC <= 0 )
    DROP 0
  THEN
  SWAP ;

: 2rshift ( ud1.l ud1.m ucount -- ud2.l ud2.m )
  \ 'ucount' must be in [0..31]
  DUP 0 32 WITHIN 0= ABORT" 2rshift: assertion failure"

  ?DUP 0= IF EXIT THEN         \ No change if ucount is 0
  >R                           \ ud1.l\ud1.m, R: ucount

  R@ 17 < IF
    \ Compute overflow bits from ud1.m
    DUP 16 R@ - LSHIFT         \ ud1.l\ud1.m\ud1.m<<(16-ucount)
    
    ROT R@ RSHIFT OR \ ud1.m\(ud1.m<<(16-ucount))|ud1.l>>ucount
    SWAP R> RSHIFT
  ELSE
    R> 16 - RECURSE
    \ Simplified 16 2rshift: ( MSC <= 0, LSC <= MSC )
    NIP 0
  THEN ;

\ -------------------------------------------------------------
\ 16 bit BE code for SHA1 message digests.

: sha1.+:32 D+ ;

\ Note: the message length is truncated to 2^32-1.
\ Not a problem since we do not claim to be able to produce
\ valid result beyond 512 CELLS anyway.
: sha1.store.bitcount ( msg.bytecount 8 -- )
  UM*
    0. 56 sha1.encbuf + 2!     \ 0. to the MSC
    60 sha1.encbuf + 2! ;      \ Store the LSC

\ -------------------------------------------------------------
\ Acquire a 32 bit value stored in big endian byte order.
\ That value resides at byte offset 'index' times 4 from
\ the base fixed size buffer 'sha1.w'.
: sha1.getword:32 ( index -- 32bitvalue )
  4 * sha1.w +                 \ Pointing to byte 3
  2@ ;

\ Store '32bitvalue' in big endian byte order to the 'sha1.w'
\ array. The first byte affected resides at byte offset 'index'
\ times 4 from the base fixed size buffer 'sha1.w'.
: sha1.putword:32 ( 32bitvalue index -- )
  4 * sha1.w +                 \ Pointing to byte 3
  2! ;

\ -------------------------------------------------------------

: sha1.initvars ( -- )
  $67452301. sha1.h0 2!
  $EFCDAB89. sha1.h1 2!
  $98BADCFE. sha1.h2 2!
  $10325476. sha1.h3 2!
  $C3D2E1F0. sha1.h4 2!
  sha1.state-started sha1.state !
  0 sha1.total-bytecount !

  \ We do surrender usage of app.msgptr to the SHA1 code.
  app.msgbuf app.msgptr ! ;

\ -------------------------------------------------------------

\ Rotate 'ud1' (32bitvalue) to the left 'ucount' times.
: sha1.leftrotate:32 ( ud1 ucount -- ud2 )
  $1F AND >R                   \ ud1.l\ud1.m, R: ucount

  2DUP                     \ ud1.l\ud1.m\ud1.l\ud1.m, R: ucount
  R@ 2lshift
  \ ud1.l\ud1.m\(ud1<<ucount).l\(ud1<<ucount).m, R: ucount
  3 ROLL 3 ROLL
  \ (ud1<<ucount).l\(ud1<<ucount).m\ud1.l\ud1.m, R: ucount
  32 R> - 2rshift
  2or ;

\ -------------------------------------------------------------

: sha1.expand-block ( -- )
  sha1.encbuf sha1.w 64 CMOVE  \ Current block to 'sha1.w'

  \ Extend the sixteen 32-bit words into eighty 32-bit words
  80 16 DO
    i 3  - sha1.getword:32
    i 8  - sha1.getword:32 2xor
    i 14 - sha1.getword:32 2xor
    i 16 - sha1.getword:32 2xor
    1 sha1.leftrotate:32
    i sha1.putword:32
  LOOP ;

\ -------------------------------------------------------------

: sha1.digest-one-block ( -- )
  sha1.expand-block

  \ Per block hash value initialization.
  sha1.h0 2@ sha1.a 2!
  sha1.h1 2@ sha1.b 2!
  sha1.h2 2@ sha1.c 2!
  sha1.h3 2@ sha1.d 2!
  sha1.h4 2@ sha1.e 2!

  \ Main loop
  80 0 DO
    I 0 20 WITHIN IF
      $5A827999.
      sha1.b 2@ sha1.c 2@ 2and sha1.b 2@ 2invert
        sha1.d 2@ 2and 2or
    THEN

    I 20 40 WITHIN IF
      $6ED9EBA1.
      sha1.b 2@ sha1.c 2@ 2xor sha1.d 2@ 2xor
    THEN

    I 40 60 WITHIN IF
      $8F1BBCDC.
      sha1.b 2@ sha1.c 2@ 2and
        sha1.b 2@ sha1.d 2@ 2and 2or
        sha1.c 2@ sha1.d 2@ 2and 2or
    THEN

    I 60 80 WITHIN IF
      $CA62C1D6.
      sha1.b 2@ sha1.c 2@ 2xor sha1.d 2@ 2xor
    THEN

    \ ud-sha1-k\ud-sha1-f

    sha1.+:32
      sha1.a 2@ 5 sha1.leftrotate:32 sha1.+:32
      sha1.e 2@ sha1.+:32
      i sha1.getword:32 sha1.+:32 \ aka sha1-temp
    sha1.d 2@ sha1.e 2!
    sha1.c 2@ sha1.d 2!
    sha1.b 2@ 30 sha1.leftrotate:32 sha1.c 2!
    sha1.a 2@ sha1.b 2!
    sha1.a 2!                  \ sha1-a = sha1-temp
  LOOP

  sha1.a 2@ sha1.h0 2@ sha1.+:32 sha1.h0 2!
  sha1.b 2@ sha1.h1 2@ sha1.+:32 sha1.h1 2!
  sha1.c 2@ sha1.h2 2@ sha1.+:32 sha1.h2 2!
  sha1.d 2@ sha1.h3 2@ sha1.+:32 sha1.h3 2!
  sha1.e 2@ sha1.h4 2@ sha1.+:32 sha1.h4 2! ;

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
  sha1.h0 2@ <# # # # # # # # # #>               TYPE
  sha1.h1 2@ <# # # # # # # # # [CHAR] : HOLD #> TYPE
  sha1.h2 2@ <# # # # # # # # # [CHAR] : HOLD #> TYPE
  sha1.h3 2@ <# # # # # # # # # [CHAR] : HOLD #> TYPE
  sha1.h4 2@ <# # # # # # # # # [CHAR] : HOLD #> TYPE
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

  >R                           \ R: skip-cell-count
  DEPTH R@ ?DO
    I PICK  app.msgptr @ !
    1 CELLS app.msgptr +!
    1 CELLS app.msglen +!
  LOOP
  R> DROP

  .sha1.digest ;

\ -------------------------------------------------------------
\ Tests cases as defined in RFC 3174, at the end of the C code.

\ : target-status ( -- )
\   CR ." Target is 16 bit big endian" ;

\ : digest-sliteral ( addr bytecount -- )
\   DUP app.msglen ! app.msgbuf SWAP CMOVE
\   app.msgbuf app.msgptr !
\   .sha1.digest ;

\ target-status

\ S" abc" CR digest-sliteral
\ Expected output is:
\ A9993E36:4706816A:BA3E2571:7850C26C:9CD0D89D

\ S" abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
\   CR digest-sliteral
\ Expected output is:
\ 84983E44:1C3BD26E:BAAE4AA1:F95129E5:E54670F1

\ RFC 3174 tests that have a repeat count>1 are not supported.

\ Tests from the SHA-1 wikipedia page.
\ S" The quick brown fox jumps over the lazy dog"
\   CR digest-sliteral
\ Expected output is:
\ 2FD4E1C6:7A2D28FC:ED849EE1:BB76E739:1B93EB12

\ S" The quick brown fox jumps over the lazy cog"
\   CR digest-sliteral
\ Expected output is:
\ DE9F2C7F:D25E1B3A:FAD3E85A:0BD17D9B:100DB4B3

\ Test from https://www.di-mgt.com.au/sha_testvectors.html
\ S" " CR digest-sliteral
\ Expected output is:
\ DA39A3EE:5E6B4B0D:3255BFEF:95601890:AFD80709

