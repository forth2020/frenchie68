This is a C port of the original ANS94 Forth implementation.

This code builds properly under the following configurations:

- Linux Mint 19.3 (Ubuntu 18.04) with gcc 7.5.0 on I5 @ 3.40 GHz.
- OpenSolaris 09/06 with gcc 3.4.3 on Pentium 4 @ 3.00 GHz.
- OpenVMS 9.2-3 with VSI C V7.6-1 on VirtualBox 7.0.8, 2 vCPUs (I5 @ 3.40 GHz).

For consistency across the various platforms, the code is generated as a
32 bit ELF binary.

\ -----------------------------------------------------------------------------
\ Building the applications (VT420/VT340).

Unix:

./make.sh

VMS:

@make.com

\ -----------------------------------------------------------------------------
\ Running the application (VT420).

Unix:

./pm420

VMS:

run pm420

\ -----------------------------------------------------------------------------
\ Running the application (VT340).

Unix:

./pm340

VMS:

run pm340

