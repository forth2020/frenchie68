\ CRC32 based on the C implementation included in RFC 1952
\ (GZIP hashes). That code does not seem to depend on the
\ target endianness; it is actually simpler than the C code!
\ The following targets a 64 or 32 bit cell Forth system.

\ Tested under:
\ GForth 0.7.3 (gforth-fast)
\ SwiftForth i386-Linux 3.12.0
\ SwiftForth x64-Linux 4.0.0-RC75
\ VFX Forth 64 5.41

DECIMAL

\ The 64 bit question comes up primarily with respect to
\ SwiftForth and its upcoming 4.0 flavor (a beta at the time of
\ this writing). However, there are also 32 bit GForth flavors.
: IF64 [ 1 CELLS 8 <> ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE
: IFN64 [ 1 CELLS 8 = ] LITERAL IF POSTPONE \ THEN ; IMMEDIATE

FALSE VALUE crc32.tbl_inited

CREATE crc32.table
256 CELLS ALLOT                \ at least 32 bit cells here

\ -------------------------------------------------------------
\ RFC 1952 CRC32 implementation.

\ One time CRC32 table initialization of all 8 bit values.
: crc32.tbl_init ( -- )
  crc32.tbl_inited IF EXIT THEN

  256 0 DO
    I                          \ at least a 32 bit value
    8 0 DO                     \ c
      DUP 1 RSHIFT SWAP        \ c>>1\c
      1 AND IF
        $EDB88320 XOR
      THEN
    LOOP
    crc32.table I CELLS + !
  LOOP
  TRUE TO crc32.tbl_inited ;

\ This is designed so as to be chainable over multiple buffers.
\ The double resulting from a previous call just needs to
\ be fed back in (untested use case here!).
: crc32.updatevalue ( bufptr bytecount crcin -- crcout )
  crc32.tbl_init 

  INVERT
  IF64 $FFFFFFFF AND
  SWAP 0 DO                    \ bufptr\crcout
    OVER C@                    \ bufptr\crcout\bufptrC@
    OVER XOR                   \ bufptr\crcout\bufptrC@^crcout
    $FF AND                    \ bufptr\crcout\(c^buf[n])&0xff 
    CELLS crc32.table + @      \ bufptr\crcout\crc32.table[]
    SWAP 8 RSHIFT XOR          \ bufptr\ncrcout
    SWAP 1+ SWAP               \ nbufptr\ncrcout
  LOOP
  NIP INVERT
  IF64 $FFFFFFFF AND
  ;

: crc32.print ( bufptr bytecount -- )
  0 crc32.updatevalue
  BASE @ >R HEX
  CR S>D <# # # # # # # # # #> TYPE
  R> BASE ! ;

\ -------------------------------------------------------------
\ Test vectors from RFC 3720 Appendix A
\ Actual CRC32 results obtained collected from
\ https://www.lammertbies.nl/comm/info/crc-calculation

FALSE [IF]
  CREATE crc32.testbuffer 48 ALLOT

  \ 32 bytes of zeroes.
  crc32.testbuffer 32 erase
  crc32.testbuffer 32 crc32.print
  \ $190A55AD is expected.

  \ 32 bytes of ones.
  crc32.testbuffer 32 $FF FILL
  crc32.testbuffer 32 crc32.print
  \ $FF6CAB0B is expected.

  \ 32 bytes incrementing 0..31.
  : crc32.range-up ( addr -- )
    32 0 DO
      I OVER C!
      1+
    LOOP
    DROP ;
  crc32.testbuffer crc32.range-up
  crc32.testbuffer 32 crc32.print
  \ $91267E8A is expected.

  \ 32 bytes decrementing 31..0.
  : crc32.range-down ( addr -- )
    0 31 DO
      I OVER C!
      1+
      -1
    +LOOP
    DROP ;
  crc32.testbuffer crc32.range-down
  crc32.testbuffer 32 crc32.print
  \ $9AB0EF72 is expected.

  \ 48 bytes - iSCSI Read command PDU.
  crc32.testbuffer 48 erase
  $01 crc32.testbuffer C!
  $C0 crc32.testbuffer 1+ C!
  $14 crc32.testbuffer 16 + C!
  $04 crc32.testbuffer 22 + C!
  $14 crc32.testbuffer 27 + C!
  $18 crc32.testbuffer 31 + C!
  $28 crc32.testbuffer 32 + C!
  $02 crc32.testbuffer 40 + C!
  crc32.testbuffer 48 crc32.print
  \ $51E17412 is expected.
[THEN]

