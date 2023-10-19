\ CRC32 based on the C implementation included in RFC 1952
\ (GZIP hashes). That code does not seem to depend on the
\ target endianness; it is actually simpler than the C code!
\ The following targets a 16 bit cell Forth system.

\ Tested under:
\ Z79Forth/A

DECIMAL

FALSE VALUE crc32.tbl_inited

CREATE crc32.table
256 2* CELLS ALLOT             \ We need double cells here

\ -------------------------------------------------------------
\ Define basic double primitives.

: D>S ( d -- n )
  DROP ;

: 2invert ( ud1 -- ud2 )
  SWAP INVERT                  \ Handle the LSC
  SWAP INVERT ;                \ and then the MSC

: 2xor ( ud1 ud2 -- ud3 )
  ROT XOR                      \ Handle the MSC
  -rot XOR SWAP ;              \ and then the LSC

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
\ RFC 1952 CRC32 implementation.

\ One time CRC32 table initialization of all 8 bit values.
: crc32.tbl_init ( -- )
  crc32.tbl_inited IF EXIT THEN

  256 0 DO
    I S>D                      \ at least a 32 bit value
    8 0 DO                     \ c.
      2DUP 1 2rshift 2SWAP     \ (c.>>1).\c.
      D>S 1 AND IF
        $EDB88320. 2xor
      THEN
    LOOP
    crc32.table I 2* CELLS + 2!
  LOOP
  TRUE TO crc32.tbl_inited ;

\ This is designed so as to be chainable over multiple buffers.
\ The double resulting from a previous call just needs to
\ be fed back in (untested use case here!).
: crc32.updatevalue ( bufptr bytecount crcin. -- crcout. )
  crc32.tbl_init 

  2invert

  ROT 0 DO                  \ bufptr\crcout.
    2 PICK C@ S>D           \ bufptr\crcout.\bufptrc@.
    2OVER 2xor              \ bufptr\crcout.\bufptrc@.^crcout.
    D>S $FF AND             \ bufptr\crcout.\(c^buf[n])&0xff
    CELLS 2* crc32.table + 2@ \ bufptr\crcout.\crc32.table[].
    2SWAP 8 2rshift 2xor    \ bufptr\ncrcout.
    ROT 1+ -rot             \ nbufptr\ncrcout.
  LOOP
  2invert ROT DROP

  ;

: crc32.print ( bufptr bytecount -- )
  0. crc32.updatevalue
  BASE @ >R HEX
  CR <# # # # # # # # # #> TYPE
  R> BASE ! ;

\ -------------------------------------------------------------
\ Test vectors from RFC 3720 Appendix A.
\ Actual CRC32 results have been compared to
\ https://www.lammertbies.nl/comm/info/crc-calculation

\ Note: the test code has been validated under Z79Forth/A.
\ It is commented out since interpreted conditionals are not
\ currently supported. GNU Forth's PARSE kinda requires SOURCE
\ to have file semantics and only block semantics is
\ available. This might eventually be overcome--but not today!

\ CREATE crc32.testbuffer 48 ALLOT

  \ 32 bytes of zeroes.
\ crc32.testbuffer 32 erase
\ crc32.testbuffer 32 crc32.print
  \ $190A55AD is expected.

  \ 32 bytes of ones.
\ crc32.testbuffer 32 $FF FILL
\ crc32.testbuffer 32 crc32.print
  \ $FF6CAB0B is expected.

  \ 32 bytes incrementing 0..31.
\ : crc32.range-up ( addr -- )
\   32 0 DO
\     I OVER C!
\     1+
\   LOOP
\   DROP ;
\ crc32.testbuffer crc32.range-up
\ crc32.testbuffer 32 crc32.print
  \ $91267E8A is expected.

  \ 32 bytes decrementing 31..0.
\ : crc32.range-down ( addr -- )
\   0 31 DO
\     I OVER C!
\     1+
\     -1
\   +LOOP
\   DROP ;
\ crc32.testbuffer crc32.range-down
\ crc32.testbuffer 32 crc32.print
  \ $9AB0EF72 is expected.

  \ 48 bytes - iSCSI Read command PDU.
\ crc32.testbuffer 48 ERASE
\ $01 crc32.testbuffer C!
\ $C0 crc32.testbuffer 1+ C!
\ $14 crc32.testbuffer 16 + C!
\ $04 crc32.testbuffer 22 + C!
\ $14 crc32.testbuffer 27 + C!
\ $18 crc32.testbuffer 31 + C!
\ $28 crc32.testbuffer 32 + C!
\ $02 crc32.testbuffer 40 + C!
\ crc32.testbuffer 48 crc32.print
  \ $51E17412 is expected.

