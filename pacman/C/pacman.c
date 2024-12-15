#if defined(__sun) && defined(__SVR4)
#define FORCE_CURSES    // Force curses under OpenSolaris
#endif

#if defined(__VMS) && !defined(FORCE_CURSES)
#define FORCE_CURSES
#define _BSD44_CURSES
#endif

#include <stdint.h>
#include <termios.h>
#include <unistd.h>     // Needed for read(2)
#include <time.h>
#include <poll.h>       // Under VMS, poll() is to be used for non-sockets

#ifdef FORCE_CURSES
#include <curses.h>     // In the absence of tcgetattr()/tcsetattr()...
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

// Pacman for the DEC VT420/340. Francois Laagel. Jan-Jun 2024.
//
// "Whereof one cannot speak, thereof one must be silent."
// "Tractatus Logico-Philosophicus", Ludwig Wittgenstein, 1918.
//
// The original Forth bugs have been faithfully ported!
// More of these might have been introduced in the process.
// So it goes (KV)...

#define CLKPERIOD 170  // Expressed in milliseconds
#define NGHOST 4
#define SILENT 0
#define NENTITY (1+NGHOST)

// A clock cycle count during which PM stays "supercharged."
#define SUPER_CLKCYCLES 121

/*
 * Early design decisions:
 * - a CELL maps to an int32_t stdint data type. We operate
     in 32 bit mode.
 * - DOUBLEs are mapped to int32_t.
 */

uint16_t seed;         // Must be NZ on first use!
uint32_t hiscore;
uint32_t score;
uint32_t lives;
uint32_t gamlev;
uint32_t bonus;
uint32_t suptim;
uint32_t serialno = 0; // Instance number generator.
uint32_t nremitem = 0;

// Disable BELL if TRUE
uint32_t silent = 0;

// The entity vector.
void *entvec[NENTITY];
#define PACMAN_ADDR ((entity *)(entvec[0]))

// Forward references...
uint32_t fright_timer;
void finalize(void);
void super_enter(void);
void super_leave(void);
void *entity_new(uint8_t hcvr, uint8_t hcpc, uint8_t vrow, uint8_t pcol,
  uint8_t cdir);

// Ghost mode enumeration.
typedef enum ghostmode_t {
  mode_scatter,
  mode_chase,
  mode_fright,
  mode_unspec
} ghostmode_t;

// Those are global variables (in disguise).
uint32_t gm_cur = mode_scatter;  // Current mode
uint32_t gm_prv = mode_unspec;   // Previous mode

int32_t gm_timer_en = -1;

// ------------------------------------------------------------
// Grid specification.

#define NCOL 33
#define NROW 23
#define GRIDSIZE (NCOL * NROW)
uint8_t grid[GRIDSIZE];
#define NITEM 172     // The total number of collectible items

// ------------------------------------------------------------
// Well known symbols.
#define door   ((uint8_t)'T')
#define cross  ((uint8_t)'K')
#define pellet ((uint8_t)'L')

// ------------------------------------------------------------
// Pseudo-random number generator.

// Using John Metcalf's Xorshift LFSRs PRNG.
// http://www.retroprogramming.com/2017/07/
//   xorshift-pseudorandom-numbers-in-z80.html
uint16_t
prandom(void) {
  seed ^= seed << 7;
  seed ^= seed >> 9;
  seed ^= seed << 8;
  return seed;
}

// -------------------------------------------------------------
// Select Graphic Rendition (SGR). VT100 control sequences.
// This is particularly necessary on the VT340.

// Select 'bold' character rendition.
void
bold_sgr() {
  fputs("\x1B[1m",stdout);
}

// Select 'All attributes off' character rendition.
void
default_sgr(void) {
  fputs("\x1B[0m",stdout);
}

// ------------------------------------------------------------
// Posix terminal control routines. Need to be called in
// initialize() and finalize().

void
prep_terminal(void) {
  // Establish non-canonical input processing on fd 0
  // and disable echo of input characters.
#ifndef FORCE_CURSES                     // The POSIX.1 way
  struct termios tio;

  (void)tcgetattr(fileno(stdin), &tio);
  tio.c_lflag &= ~(ICANON | ECHO);
  tio.c_cc[VMIN] = 1;
  tio.c_cc[VTIME] = 0;
  (void)tcsetattr(fileno(stdin), TCSANOW, &tio);
#else                                    // The curses way
  initscr();                             // Initialize curses library.
  noecho();                              // Turn echo off

  // Switch to cbreak mode
#ifndef _BSD44_CURSES
  cbreak();                              // SVR4 and Linux
#else
  crmode();                              // BSD 4.4 under VMS
#endif                                   // _BSD44_CURSES
#endif                                   // FORCE_CURSES

  setbuf(stdout, NULL);
  setbuf(stdin, NULL);
}

void
unprep_terminal(void) {
#ifndef FORCE_CURSES                     // The POSIX.1 way
  struct termios tio;

  (void)tcgetattr(fileno(stdin), &tio);
  tio.c_lflag |= ICANON | ECHO;
  (void)tcsetattr(fileno(stdin), TCSANOW, &tio);
#else
  endwin();                              // The curses way
  setbuf(stdout, NULL);
#endif
}

// ------------------------------------------------------------
// Cursor control. VT200 control sequences.

void
disable_cursor(void) {
  fputs("\x1B[?25l", stdout);
}

void
enable_cursor(void) {
  fputs("\x1B[?25h", stdout);
}

// Select custom character set.
void
custom_charset_select(void) {
  putchar(14);                           // GL <- G1 (LS1 locking shift)
}

// Select default character set.
void
default_charset_select(void) {
  putchar(15);                           // GL <- G0 (LS0 locking shift)
}

// ------------------------------------------------------------
// Forth support primitives: AT-XY PAGE CR MS KEY? KEY

void
at_xy(int x, int y) {
  printf("\x1B[%d;%dH", 1 + y, 1 + x);
}

// Clear the screen. VT100 style.
void
page(void) {
  fputs("\x1B[H\x1B[J\x0D", stdout);
}

void
cr(void) {
  putchar(10);
}

void
ms(uint32_t nms) {
  struct timespec rqt;

  rqt.tv_sec = nms / 1000;
  rqt.tv_nsec = (nms % 1000) * 1000 * 1000;
  (void)nanosleep(&rqt, NULL);
}

uint32_t
key_question(void) {
  struct pollfd pfds[1];
  int retval;

  pfds[0].fd = fileno(stdin);
  pfds[0].events = POLLIN;
  retval = poll(pfds, (nfds_t)1, 1);
  if (retval == -1) {
    default_sgr();
    unprep_terminal();
    default_charset_select();
#ifndef __VMS
    at_xy(0, 23);
#else
    at_xy(0, 22);                        // Why???
#endif
    setbuf(stderr, NULL);
    perror("poll() failed");
    enable_cursor();
    exit(1);
  }
  return retval == 1;
}

// Note: this will be blocking unless a previous call to
// key_question() returned NZ.
uint8_t
key(void) {
// Bypass curses for all terminal I/Os. The library is way too smart.
  uint8_t val;

  (void)read(fileno(stdin), &val, 1);
  return val;
}

// ------------------------------------------------------------
// VT420/VT340 specific material.

const uint32_t pfn = 1;
const uint32_t pcn = 1;                  // First soft character at $21
const uint32_t pe = 1;                   // Erase only new definitions
#define PCMW 10                          // Chr width is 10 pix in 80 col mode
const uint32_t pss = 0;                  // 80 columns, 24 lines
const uint32_t pt = 2;                   // Full cell

#ifdef VT420
#define PCMH 16                          // Chr height is 16: 6/6/4 in sixels
#elif defined(VT340)
#define PCMH 20                          // Chr height is 20: 6/6/6/2 in sixels
#else
#error "Unsupported target terminal"
#endif

const uint32_t pcss = 0;                 // 94-charset
const uint8_t ufn = 'U';                 // User font name. Argument to DSCS

#define NSIXEL ((PCMH + 5) / 6) // Sixels per column

void
dscs(void) {
  putchar(ufn);
}

// Define character set.
void
dcs(void) {
  fputs("\x1BP", stdout);
}

// Emit string terminator.
void
st(void) {
  fputs("\x1B\\", stdout);
}

// Emit a semi-column character.
void
semcol_emit(void) {
  putchar(';');
}

// Ghosts are: Blinky (red), Pinky (pink), Inky (cyan)
// and Clyde (orange). This is a monochrome rendition so that
// effect will be lost...

#ifdef VT420
#include "sf420-hex.c"
#else
#include "sf340-hex.c"
#endif

// The following is twice the number of double width chars.
#define NCHAR (((int)sizeof(softfont))/(PCMW*NSIXEL))

void
softfont_emit(void) {
  int i, j, k;

  for (k = 0; k < NCHAR; k++) {          // Iterate over char. defs
    for (j = 0; j < NSIXEL; j++) {       // Iterate over sixel groups
      for (i = 0; i < PCMW; i++)         // Iterate over col. defs
        putchar('?' + softfont[k][i][j]);
      if (j != NSIXEL - 1)
        putchar('/');                    // Group delimiter
    }
    if (k != NCHAR - 1)
      semcol_emit();                     // Character delimiter
  }
}

void
decsend(uint8_t c) {
  printf("%u", (unsigned)c);
}

// DECDLD spec:
// DCS Pfn; Pcn; Pe; Pcmw; Pss; Pt; Pcmh; Pcss { Dscs
// Sxbp1 ; Sxbp2 ;...; Sxbpn ST
void
decdld(void) {
  dcs();
  decsend(pfn);  semcol_emit(); decsend(pcn);  semcol_emit();
  decsend(pe);   semcol_emit(); decsend(PCMW); semcol_emit();
  decsend(pss);  semcol_emit(); decsend(pt);   semcol_emit();
  decsend(PCMH); semcol_emit(); decsend(pcss);
  putchar('{'); dscs();
  softfont_emit();
  st();

  // Charset designation.
  fputs("\x1B)", stdout); dscs();        // G1 <- <UserFontName>
}

// Used by PM when entering/leaving the "supercharged" state.
void
bell(void) {
  if (silent)
    return;

  default_charset_select();
  putchar(7);
  custom_charset_select();
}

// ------------------------------------------------------------

// We define this enumeration so that opposite(dir) is
// dir 2 + 3 AND (modulo 4) for dir in [0..3].
typedef enum dir_t {
  dir_up,
  dir_left,
  dir_down,
  dir_right,
  dir_blocked,                           // Must be 1 + dir_right
  dir_unspec,                            // Invalid except for idir (pacman)
  dir_quit                               // Inv. exc. as retval/pacman.dirselect
} dir_t;

void
entity_vector_init(void) {
  // By convention, we have PM as instance #0.
  // This is a central assumption though!
  entvec[0] = entity_new(-1, -1, 34, 32, dir_right);

  // Blinky is entity #1, Red, default design. North central ghost.
  entvec[1] = entity_new(4, 60, 14, 32, dir_left);

  // Pinky is entity #2, Pink, frowning. Central ghost.
  entvec[2] = entity_new(4, 2, 20, 32, dir_up);

  // Inky is entity #3, Cyan, nosy. Western ghost.
  entvec[3] = entity_new(40, 62, 20, 30, dir_down);

  // Clyde is entity #4, Orange, smiling, Eastern ghost.
  entvec[4] = entity_new(40, 2, 20, 34, dir_left);
}

void
initvars(void) {
  serialno = 0;
  entity_vector_init();

  hiscore = 0;      // Make this somehow persistent!
  score = 0;
  lives = 3;
  gamlev = 0;
  bonus = 0;
  suptim = 0;
  gm_timer_en = -1; // Enable ghost mode scheduler
  nremitem = 0;     // Force level entry initializations
}

void
finalize(void) {
  default_sgr();
  unprep_terminal();
  default_charset_select();

#ifdef __VMS               // XXX Why do we have to do that?
  at_xy(0, 11);
  fputs("        ", stdout);
#endif

  at_xy(0, 23);
  fputs("Interrupted!", stdout);
#ifndef __VMS              // DCL does that for us!
  cr();
#endif
  enable_cursor();
  exit(0);
}

void
init_signal_processing(void) {
  struct sigaction sac;

  (void)sigemptyset(&sac.sa_mask);
  sac.sa_handler = (void (*)(int))finalize;
  sac.sa_flags = 0;
  (void)sigaction(SIGINT, &sac, NULL);
}

void
initialize(void) {
  initvars();
  prep_terminal();
  page();
  disable_cursor();        // Cursor off
  fputs("\x1B F", stdout); // 7-bit C1 control characters
  bold_sgr();
  decdld();                // Upload charset definition
  custom_charset_select(); // Select custom character set
  init_signal_processing();
}

void
dot_var(uint32_t var) {
  printf("%08d", var);
}

void
update_score(uint32_t delta) {
  score += delta;
  default_charset_select();
  at_xy(0, 4);
  dot_var(score);
  custom_charset_select();
}

void
update_lives(void) {
  lives--;                 // Always goes down!
  default_charset_select();
  at_xy(0, 7);
  dot_var(lives);
  custom_charset_select();
}

void
update_level(void) {
  gamlev++;
  default_charset_select();
  at_xy(0, 10);
  dot_var(gamlev);
  custom_charset_select();
}

void
update_suptim(void) {
  suptim += CLKPERIOD / 5;
  default_charset_select();
  at_xy(0, 16);
  dot_var(suptim);
  custom_charset_select();
}

// This routine should only be called when the default character
// set is in effect. Otherwise things will look ugly.
void
dot_sitrep(void) {
  at_xy(0, 1);  dot_var(hiscore);
  at_xy(0, 4);  dot_var(score);
  at_xy(0, 7);  dot_var(lives);
  at_xy(0, 10); dot_var(gamlev);
  at_xy(0, 13); dot_var(bonus);
  at_xy(0, 16); dot_var(suptim);
}

// Print status headers. Forces in the default character set and
// leaves in custom character set mode.
void
dot_init_sitrep(void) {
  default_charset_select();
  at_xy(0, 0);  fputs("Highscore", stdout);
  at_xy(0, 3);  fputs("Score", stdout);
  at_xy(0, 6);  fputs("Lives", stdout);
  at_xy(0, 9);  fputs("Level", stdout);
  at_xy(0, 12); fputs("Bonus", stdout);
  at_xy(0, 15); fputs("Supertime", stdout);
  dot_sitrep();
  custom_charset_select();
}

// Grid definition language:
// BL     2 SPACES
// CHAR A upper left corner
// CHAR B upper right corner
// CHAR C Lower left corner
// CHAR D Lower right corner
// CHAR E Horizontal bar
// CHAR F Vertical bar
// CHAR G T down
// CHAR H T up
// CHAR I T left
// CHAR J T right
// CHAR K Cross
// CHAR L Power pellet
// CHAR M Pacman going right
// CHAR N Ghost (Blinky)
// CHAR O West
// CHAR P East
// CHAR Q South
// CHAR R Pacman (gobbling)
// CHAR S North
// CHAR T Door
// CHAR U Pacman going left
// CHAR V Pacman going upward
// CHAR W Pacman going downward
// CHAR X Ghost (Inky)
// CHAR Y Ghost (Pinky)
// CHAR Z Ghost (Clyde)
// CHAR [ Ghost (Blinky) in reverse video
// CHAR \ Ghost (Inky) in reverse video
// CHAR ] Ghost (Pinky) in reverse video
// CHAR ^ Ghost (Clyde) in reverse video -- see also dot_grid_char

// IMPORTANT NOTE: the user defined font character definition
// has been re-arranged from the Forth definition, so as to
// simplify the C code.

#define X0 (80 - 2 * NCOL)

// A variant of finalize().
void
crash_and_burn(char *errmsg) {
  default_sgr();
  unprep_terminal();
  default_charset_select();
  at_xy(0, 23);
  fputs(errmsg, stdout);
#ifndef __VMS              // DCL does that for us!
  cr();
#endif
  enable_cursor();
  exit(0);
}

// Display doublewidth character at offset 'c'.
// 0x21 is the first user defined character.
void
dot_dwchar(uint8_t c) {
  c += 0x21;
  printf("%c%c", c, 1 + c);
}

void
dot_grid_char(uint8_t gc) {
  if (gc == ' ') {
    fputs("  ", stdout);
    return;
  }

  // Defensive programming.
  if (!(gc >= 'A' && gc <= '^'))
    crash_and_burn("dot_grid_char: illegal character");

  dot_dwchar((gc - 'A') << 1);
}

// Directly (Yeah?) referenced DW character printing primitives.
void
dot_ulc(void) {
  dot_grid_char('A');
}

void
dot_urc(void) {
  dot_grid_char('B');
}

void
dot_llc(void) {
  dot_grid_char('C');
}

void
dot_lrc(void) {
  dot_grid_char('D');
}

void
dot_hbar(void) {
  dot_grid_char('E');
}

void
dot_vbar(void) {
  dot_grid_char('F');
}

void
dot_tdn(void) {
  dot_grid_char('G');
}

void
dot_tup(void) {
  dot_grid_char('H');
}

void
dot_tlf(void) {
  dot_grid_char('I');
}

void
dot_trg(void) {
  dot_grid_char('J');
}

void
dot_cross(void) {
  dot_grid_char(cross);
}

void
dot_ppl(void) {
  dot_grid_char(pellet);
}

void
dot_pmrgt(void) {
  dot_grid_char('M');
}

// #define DOT_BLINKY dot_grid_char('N')
void
dot_blinky(void) {
  dot_grid_char('N');
}

void
dot_west(void) {
  dot_grid_char('O');
}

void
dot_east(void) {
  dot_grid_char('P');
}

void
dot_south(void) {
  dot_grid_char('Q');
}

void
dot_pmgo(void) {
  dot_grid_char('R');
}

void
dot_north(void) {
  dot_grid_char('S');
}

void
dot_door(void) {
  dot_grid_char(door);
}

void
dot_pmlft(void) {
  dot_grid_char('U');
}

void
dot_pmupw(void) {
  dot_grid_char('V');
}

void
dot_pmdnw(void) {
  dot_grid_char('W');
}

void
dot_inky(void) {
  dot_grid_char('X');
}

void
dot_pinky(void) {
  dot_grid_char('Y');
}

void
dot_clyde(void) {
  dot_grid_char('Z');
}

void
dot_rblinky(void) {
  dot_grid_char('[');
}

void
dot_rinky(void) {
  dot_grid_char('\\');
}

void
dot_rpinky(void) {
  dot_grid_char(']');
}

void
dot_rclyde(void) {
  dot_grid_char('^');
}

void
display_line(char *saddr, uint32_t lineno) {
  uint32_t i;

  if (strlen(saddr) != NCOL)
    crash_and_burn("display_line: incorrect column count");

  at_xy(X0, lineno);
  for (i = 0; i < NCOL; i++) {
    grid[lineno * NCOL + i] = saddr[i]; // Grid initialization.

    dot_grid_char(saddr[i]);
  }
}

// Display the initial grid contents.
// Note: this assumes custom-charset-select is in effect.
// By design no instanciated object should be referenced here.
void
dot_initial_grid(void) {
  // 33 columns (double width characters) by 23 rows.
  display_line("AEEEEEEEGEEEEEEEEEEEEEEEGEEEEEEEB", 0);
  display_line("FL K K KFK K K K K K K KFK K K LF", 1);
  display_line("F AEEEP Q OEEEEEEEEEEEP Q OEEEB F", 2);
  display_line("FKFK K K K K K K K K K K K K KFKF", 3);
  display_line("F Q S S OEP OEEEEEEEP OEP S S Q F", 4);
  display_line("FK KFKFK K K K K K K K K KFKFK KF", 5);
  display_line("JEP F Q OEEEB OEEEP AEEEP Q F OEI", 6);
  display_line("FK KFK K K KFK K K KFK K K KFK KF", 7);
  display_line("F S Q OEEEB F ATTTB F AEEEP Q S F", 8);
  display_line("FKFK K K KFKFKF   FKFKFK K K KFKF", 9);
  display_line("F F OEEEP F F F   F F F OEEEP F F", 10);
  display_line("FKFK K K KFKFKF   FKFKFK K K KFKF", 11);
  display_line("F CEP S S Q Q CEEED Q Q S S OED F", 12);
  display_line("FK K KFKFK K K K K K K KFKFK K KF", 13);
  display_line("F OEEED Q S OEEEEEEEP S Q CEEEP F", 14);
  display_line("FK K K K KFK K K K K KFK K K K KF", 15);
  display_line("F OEGEEEP Q OEEEEEEEP Q OEEEGEP F", 16);
  display_line("FK KFK K K K K K K K K K K KFK KF", 17);
  display_line("JEP F OEP S OEEEEEEEP S OEP F OEI", 18);
  display_line("FK KFK K KFK K K K K KFK K KFK KF", 19);
  display_line("F OEHEEEP F OEEEEEEEP F OEEEHEP F", 20);
  display_line("FL K K K KFK K K K K KFK K K K LF", 21);
  display_line("CEEEEEEEEEHEEEEEEEEEEEHEEEEEEEEED", 22);
  nremitem = NITEM;
}

// ------------------------------------------------------------
// Animation objects.

typedef void (*method)(void *);

// Caution here: some of the 8 bit fields may have to be signed!
typedef struct entity {
  method  strategy; // Strategy (moving) method
  method  display;  // Display method
  uint8_t resurr;   // # Clock ticks till we're back (ghosts)
  uint8_t reward;   // # points for killing a ghost / 100 (PM)
  uint8_t vrown;    // Virtual row number
  uint8_t pcoln;    // Physical column number
  uint8_t ivrown;   // Interfering virtual row number (ghosts)
  uint8_t ipcoln;   // Interfering pcol number (ghosts)
  uint8_t igchr;    // Interfering grid character (ghosts)
  uint8_t pcol0;    // Initial pcol number
  uint8_t vrow0;    // Initial vrow number
  uint8_t dir0;     // Initial direction
  uint8_t hcvrn;    // Home corner vrow# (ghosts)
  uint8_t hcpcn;    // Home corner pcol# (ghosts)
  uint8_t cdir;     // Current direction
  uint8_t pdir;     // Previous direction
  uint8_t idir;     // Intended direction (PM)
  uint8_t revflg;   // Reverse direction directive (ghosts)
  uint8_t inited;   // TRUE if first display has been performed
  uint8_t gobbling; // # Clock ticks till we're fed (PM)
  uint8_t inum;     // Instance serial number
} entity;

void
dot_pacman(void) {
  uint8_t seldir;   // PM's current moving direction

  if (PACMAN_ADDR->gobbling) {
    dot_pmgo();     // Display pacman as gobbling
    PACMAN_ADDR->gobbling--;
    return;
  }

  seldir = PACMAN_ADDR->cdir == dir_blocked ?
    PACMAN_ADDR->pdir : PACMAN_ADDR->cdir;
  switch (seldir) {
    case dir_right:
      dot_pmrgt();
      return;
    case dir_left:
      dot_pmlft();
      return;
    case dir_up:
      dot_pmupw();
      return;
    case dir_down:
      dot_pmdnw();
      return;
  }

  crash_and_burn("dot_pacman: invalid current direction");
}

void
entity_display(entity *self) {
  if (!self->inum) {
    dot_pacman();
    return;
  }

  if (fright_timer)
    switch (self->inum) {
      case 1:
        dot_rblinky();
        return;
      case 2:
        dot_rinky();
        return;
      case 3:
        dot_rpinky();
        return;
      case 4:
        dot_rclyde();
        return;
    }
  else
    switch (self->inum) {
      case 1:
        dot_blinky();
        return;
      case 2:
        dot_inky();
        return;
      case 3:
        dot_pinky();
        return;
      case 4:
        dot_clyde();
        return;
    }

  crash_and_burn("entity_display: unknown instance number");
}

uint32_t
bitclear(uint32_t val, uint32_t bitno) {
  return val & (~(1 << bitno));
}

uint32_t
is_bitset(uint32_t val, uint32_t bitno) {
  return val & (1 << bitno);
}

uint32_t
to_grid_space(uint32_t pcol) {
  return pcol >> 1;
}

// If moving horizontally, the resulting pcol must be
// >= 2 and < 64.
// TODO: does the parameter really need to be passed as a 32 bit value?
uint8_t
is_valid_pcol(uint32_t pcol) {
  return pcol >=2 && pcol < 64;
}

// If moving vertically, the resulting vrow number must be
// >= 2 and < 44.
// TODO: does the parameter really need to be passed as a 32 bit value?
uint8_t
is_valid_vrow(uint32_t vrow) {
  return vrow >=2 && vrow < 44;
}

uint8_t
is_scorable(uint8_t uchar) {
  return uchar == cross || uchar == pellet;
}

uint8_t
is_erasable(uint8_t uchar) {
  return uchar == ' ' || is_scorable(uchar);
}

uint8_t
is_erasable_or_door(uint8_t uchar) {
  return uchar == door || is_erasable(uchar);
}

uint8_t
in_ghosts_pen(entity *self) {
  uint8_t vrow = self->vrown,
    pcol = self->pcoln;

  return vrow >= 16 && vrow < 23 &&
    pcol >= 30 && pcol < 35;
}

// pcol and vrow are supposed to have been previously validated.
uint8_t *
get_grid_char_addr(uint8_t pcol, uint8_t vrow) {
  return grid + (NCOL * to_grid_space(vrow)) + to_grid_space(pcol);
}

// Returns the grid character at [vrow, pcol].
uint8_t
get_grid_char(uint8_t pcol, uint8_t vrow) {
  // Enforce assumptions.
  if (!is_valid_vrow(vrow))
    crash_and_burn("get_grid_char: vrow is out of bounds");
  if (!is_valid_pcol(pcol))
    crash_and_burn("get_grid_char: pcol is out of bounds");

  return *get_grid_char_addr(pcol, vrow);
}

// Note: ghost_dirselect() guarantees us that both pcoln and
// vrown are even. TODO: what about PM's moving policy???
uint8_t
can_move_in_dir(entity *self, uint8_t dir) {
  uint8_t vrow = self->vrown,
    pcol = self->pcoln,
    grid_char;

  switch (dir) {
    case dir_left:
      if (!is_valid_pcol(pcol -= 2))
        return 0;
      break;
    case dir_right:
      if (!is_valid_pcol(pcol += 2))
        return 0;
      break;
    case dir_up:
      if (!is_valid_vrow(vrow -= 2))
        return 0;
      break;
    case dir_down:
      if (!is_valid_vrow(vrow += 2))
        return 0;
      break;
    default:
      crash_and_burn("can_move_in_dir: invalid dir");
  }

  grid_char = get_grid_char(pcol, vrow);
  // The grid character might not be considered as an
  // erasable and still may be if:
  // 1: the grid character is 'T' (ghosts' pen door) AND
  // 2: we're a ghost (i.e. not pacman) AND
  // 3: the originating coordinates are inside the ghosts'
  //    pen.
  // In essence, the ghosts' pen door _is_ an erasable but
  // only for the ghosts when they are inside of the pen.
  return is_erasable(grid_char) || // Still need to check for walls!!!
    ((grid_char == door) &&        // Ghosts' pen door
      (self->inum != 0) &&         // We are not pacman
      in_ghosts_pen(self));
}

// Re-display an erasable that was at least partially obscured
// by a ghost passing by.
void
dot_interfering(entity *self) {
  if (!self->igchr)
    return;

  at_xy(X0 + self->ipcoln, to_grid_space(self->ivrown));
  dot_grid_char(self->igchr);
}

// Utility routine--not a method.
void
entity_reset_coords_and_dir(entity *self) {
  self->cdir = self->dir0;
  self->vrown = self->vrow0;
  self->pcoln = self->pcol0;
}

void
pacman_dying_routine(void) {
  uint8_t i, j;
  uint8_t prow = to_grid_space(PACMAN_ADDR->vrown),
    pcol = X0 + PACMAN_ADDR->pcoln;
  entity *ep;

  for (i = 0; i < 4; i++)   // 4 self rotations
    for (j = dir_up; j < dir_blocked; j++) {
       PACMAN_ADDR->cdir = j;
       at_xy(pcol, prow);
       dot_pacman();
       ms(125);
    }
  at_xy(pcol, prow);
  dot_grid_char(' ');

  fright_timer = 0;         // PM no longer "supercharged"
  PACMAN_ADDR->reward = 0;  // Reset the 'reward' field

  // Every entity returned to its original upright position.
  for (i = 0; i < NENTITY; i++) {
    ep = (entity *)entvec[i];

    // Blank current entity location.
    at_xy(X0 + ep->pcoln, to_grid_space(ep->vrown));
    dot_grid_char(' ');

    if (i) {
      // Restore potentially obscured character.
      dot_interfering(ep);

      // Also clear the possible interference record.
      ep->igchr = 0;

      // Keep the ghosts mostly harmless for a little time.
      ep->resurr = 20;
    }

    // Generic death handling.
    entity_reset_coords_and_dir(ep);
    ep->inited = 0;
  }
}

// TODO: omitted debugging support code.

dir_t
keyboard_input_query(void) {
  uint8_t inp;

  if(!key_question())
    return dir_unspec;       // No input at this time

  inp = key();
  if (inp == 'q')
    return dir_quit;
  if (inp != '\x1B')
    return dir_unspec;

  if (key() != '[')
    return dir_unspec;

  // CSI has been parsed, so far.
  switch (key()) {
    case 'A':
      return dir_up;
    case 'B':
      return dir_down;
    case 'C':
      return dir_right;
    case 'D':
      return dir_left;
  }

  return dir_unspec;     // No comprendo
}

uint8_t
is_pacman_stepped_on(entity *ghost) {
  uint8_t pm_grow, pm_gcol;

  if (!ghost->inum)      // This cannot be applied to PM itself!!!
    crash_and_burn("is_pacman_stepped_on: applied to PM");

  pm_grow = to_grid_space(PACMAN_ADDR->vrown);
  pm_gcol = to_grid_space(PACMAN_ADDR->pcoln);
  return (pm_grow == to_grid_space(ghost->vrown)) &&
    (pm_gcol == to_grid_space(ghost->pcoln));
}

dir_t
pacman_dirselect(entity *self) {
  uint8_t dir;
  dir_t rv;

  // Keyboard input overrides any previous intended direction.
  dir = keyboard_input_query();
  if (dir != dir_unspec) {
    if (dir == dir_quit)
      crash_and_burn("pacman_dirselect: Exiting game");

    // If a direction change is requested via keyboard input:
    // mark it as the intended direction (idir) and proceed.
    if (dir < dir_blocked)
      self->idir = dir; 
  }

  // No direction changes unless both vrow# and pcol# are even.
  if ((self->vrown & 1) || (self->pcoln & 1))
    return (dir_t)(self->cdir);

  // If idir is not dir_unspec AND we can move in idir:
  // - queue up idir as the return value.
  // - reset idir to dir_unspec.
  // - end of story.
  if (self->idir != dir_unspec &&
    can_move_in_dir(self, self->idir)) {
      rv = (dir_t)(self->idir);
      self->idir = dir_unspec;
      return rv;
  }

  // Default policy: keep the current direction unless blocked.
  if (self->cdir == dir_blocked)
    return dir_blocked;

  if (can_move_in_dir(self, self->cdir))
    return (dir_t)(self->cdir);

  self->pdir = self->cdir;
  return dir_blocked;
}

// This is a tricky one since the original Forth code returns
// FALSE|dir\TRUE, i.e. a variable outcome. We can't have that
// kind of flexibility in C.
int8_t
only_one_dir(uint32_t bm) {
  switch (bm) {
    case 1:
      return 0;
    case 2:
      return 1;
    case 4:
      return 2;
    case 8:
      return 3;
  }

  return -1;     // For the lack of a better alternative...
}

// The following implements the frightened ghost mode.
// 'bitmap' has the superposition of viable alternatives, in terms
// of possible directions for a ghost.
dir_t
ghost_dirselect_fright(entity *ep, uint32_t bitmap) {
  uint8_t bit0;
  dir_t dir;

  (void)ep;           // The parameter is passed and ignored. So it goes...

  for (dir = dir_up; dir < dir_blocked; dir++) {
    bit0 = bitmap & 1;
    bitmap >>= 1;
    if (bit0) {       // dir is an option
      if (bitmap) {   // There are other possible directions
        if (prandom() & 8)
          return dir; // Select direction 'dir'
      }
      else            // There are no alternatives left
        return dir;
    }
  }

  crash_and_burn("ghost_dirselect_fright: no viable direction found");

  // Avoid useless compiler warning.
  return dir_down;
}

// For every bit set in bitmap, we need to evaluate the
// Euclidian distance between the potential next location and
// the target tile. Finally we return the direction that
// minimizes the distance.
dir_t
ghost_dirselect_nav2target(entity *self, uint32_t bitmap, int8_t tvr,
  int8_t tpc) {
  int8_t pcol, vrow;
  uint16_t minval = 65535, minnew;
  int16_t dx, dy;
  dir_t dir, dirmin = (dir_t)-1;

  for (dir = dir_up; dir < dir_blocked; dir++) {
    if (is_bitset(bitmap, dir)) {
      pcol = (int8_t)self->pcoln;
      vrow = (int8_t)self->vrown;

      // Need to project into the next potential coordinates (in virtual space).
      switch (dir) {
        case dir_left:
          pcol--;
          break;
        case dir_right:
          pcol++;
          break;
        case dir_up:
          vrow--;
          break;
        case dir_down:
          vrow++;
          break;
        default:
          crash_and_burn("ghost_dirselect_nav2target: unrecognized current "
            "direction");
      }

      // We compare the distance to the target squared.
      dx = ((int16_t)pcol) - ((int16_t)tpc);
      dy = ((int16_t)vrow) - ((int16_t)tvr);
      minnew = dx * dx + dy * dy;
      if (minnew < minval) {
        dirmin = dir;
        minval = minnew;
      }
    }
  }

  if (dirmin == (dir_t)-1)
    crash_and_burn("ghost_dirselect_nav2target: no minimum found");

  return dirmin;
}

// In scatter mode, simply navigate to the ghost home corner.
dir_t
ghost_dirselect_scatter(entity *self, uint32_t bitmap) {
  return ghost_dirselect_nav2target(self, bitmap, self->hcvrn, self->hcpcn);
}

dir_t
ghost_dirselect_chase(entity *self, uint32_t bitmap) {
  int8_t pcol, vrow;
  entity *bp;
  dir_t dir;

  // Blinky handling. The target is PM's current location.
  if (self->inum == 1)
    return ghost_dirselect_nav2target(self, bitmap, PACMAN_ADDR->vrown,
      PACMAN_ADDR->pcoln);

  // Pinky handling. The target is 8 half tiles in PM's
  // current moving direction. It might be off the grid but
  // that does not matter in the least.
  if (self->inum == 2) {
    // Project PM's future location based on its current direction
    // by 8 tiles in virtual space.
    vrow = (int8_t)PACMAN_ADDR->vrown;
    pcol = (int8_t)PACMAN_ADDR->pcoln;


    // PM maybe blocked. If it is, act on 'pdir' instead of 'cdir'.
    dir = PACMAN_ADDR->cdir != dir_blocked ?
      PACMAN_ADDR->cdir : PACMAN_ADDR->pdir;
    switch (dir) {
      case dir_left:
        pcol -= 8;
        break;
      case dir_right:
        pcol += 8;
        break;
      case dir_up:
        vrow -= 8;
        break;
      case dir_down:
        vrow += 8;
        break;
      default:
        crash_and_burn("ghost_dirselect_chase: PM's current direction "
          "not recognized (Pinky)");
    }
    return ghost_dirselect_nav2target(self, bitmap, vrow, pcol);
  }

  // Inky handling. The target is at the end of a vector twice
  // as long as the one originating from Blinky to PM's moving
  // direction extrapolated by 4 half tiles.
  if (self->inum == 3) {
    vrow = (int8_t)PACMAN_ADDR->vrown;
    pcol = (int8_t)PACMAN_ADDR->pcoln;

    // PM maybe blocked. If it is, act on 'pdir' instead of 'cdir'.
    dir = PACMAN_ADDR->cdir != dir_blocked ?
      PACMAN_ADDR->cdir : PACMAN_ADDR->pdir;
    switch (dir) {
      case dir_left:
        pcol -= 4;
        break;
      case dir_right:
        pcol += 4;
        break;
      case dir_up:
        vrow -= 4;
        break;
      case dir_down:
        vrow += 4;
        break;
      default:
        crash_and_burn("ghost_dirselect_chase: PM's current direction "
          "not recognized (Inky)");
    }

    // For the record, Blinky is entity #1 in entvec.
    bp = (entity *)(entvec[1]);
    vrow = 2 * (vrow - bp->vrown);  // This is a delta on Y 
    pcol = 2 * (pcol - bp->pcoln);  // This is a delta on X 

    // The relative displacement refers to Blinky's current pos.
    return ghost_dirselect_nav2target(self, bitmap,
      bp->vrown + vrow, bp->pcoln + pcol);
  }

  // Default policy. Will only apply to Clyde--permanently
  // frightened in chase mode.
  return ghost_dirselect_fright(self, bitmap);
}

// From the "pacman dossier:"
// "Ghosts are forced to reverse direction by the system anytime
// the mode changes from: chase-to-scatter, chase-to-frightened,
// scatter-to-chase, and scatter-to-frightened. Ghosts do not
// reverse direction when changing back from frightened to chase
// or scatter modes."
//
// Interpreting the gospel:
// - 'reversing direction' means selecting opposite(cdir).
//
// The direction returned is guaranteed to be adopted by the
// caller.
dir_t
ghost_dirselect(entity *self) {
  uint8_t bitmap = 0X0F;     // The sum of 'a priori' alternatives
  uint8_t revreq = self->revflg;
  dir_t dir;

  // No direction changes unless both vrow# and pcol# are even.
  if ((self->vrown & 1) || (self->pcoln & 1))
    return (dir_t)(self->cdir);

  if (revreq)               // Direction reversal is requested
    self->revflg = 0;
  else                      // Exclude opposite(cdir)
    bitmap = bitclear(bitmap, (self->cdir + 2) & 3);

  // Ascertain which directions are possible.
  for (dir = dir_up; dir < dir_blocked; dir++)
    if (is_bitset(bitmap, dir) &&
      !can_move_in_dir(self, dir))
      bitmap = bitclear(bitmap, dir);

  // If we are inside of the ghosts' pen and the current
  // direction remains open, ignore revflg and stick to that.
  if (in_ghosts_pen(self) && is_bitset(bitmap, self->cdir))
    return (dir_t)(self->cdir);

  // Honor direction reversal requests.
  if (revreq)
    return (dir_t)((self->cdir + 2) & 3);

  // Optimization: if bitmap is a power of two--only one
  // direction is viable--return this direction immediately.
  if ((dir = only_one_dir(bitmap)) != (int8_t)-1)
    return dir;

  // Ghost mode dependent behaviour.
  switch (gm_cur) {
    case mode_fright:
      return ghost_dirselect_fright(self, bitmap);
    case mode_scatter:
      return ghost_dirselect_scatter(self, bitmap);
    case mode_chase:
      return ghost_dirselect_chase(self, bitmap);
  }

  crash_and_burn("ghost_dirselect: unsupported ghost mode");

  // Avoid useless compiler warning.
  return dir_down;
}

// Utility routine--not a method.
void
entity_initial_display(entity *self) {
  at_xy(X0 + self->pcoln, to_grid_space(self->vrown));
  self->display(self);
}

// Utility routine--not a method.
void
entity_get_new_coordinates(entity *self, uint8_t *pcnew, uint8_t *vrnew) {
  *pcnew = self->pcoln;
  *vrnew = self->vrown;

  // Handling a resurrecting/grounded ghost.
  if (self->resurr) {
    self->resurr--;
    return;
  }

  switch (self->cdir) {
    case dir_left:
      (*pcnew)--;
      break;
    case dir_right:
      (*pcnew)++;
      break;
    case dir_up:
      (*vrnew)--;
      break;
    case dir_down:
      (*vrnew)++;
      break;
    // dir_blocked (PM only): fall through.
  }
}

// Utility routine--not a method.
// Do not preserve erasables. Manage gobbling aspect. This
// requires an update to 'grid'. Update the score accordingly.
void
pacman_moving_policy(entity *self, uint8_t pcnew, uint8_t vrnew) {
  uint8_t gc;

  // No change unless both 'pcnew' and 'vrnew' both are even.
  if ((pcnew & 1) || (vrnew & 1))
    return;

  // Return immediately unless we have just consumed a cross or a pellet.
  if (!is_scorable(gc = get_grid_char(pcnew, vrnew)))
    return;

  self->gobbling = 2;    // Gobble for two clock cycles

  switch (gc) {
    case cross:
      update_score(10);
      break;
    case pellet:
      update_score(50);
      // Enter "supercharged" mode
      // Note: we do not reset the 'reward' field here.
      // Maybe we should--or not. This is a possible way
      // to achieve wicked scores!!!
      super_enter();
      break;
  }

  // Cross or pellet consumed. Blank the grid character.
  *get_grid_char_addr(pcnew, vrnew) = (uint8_t)' ';

  if (nremitem)
    nremitem--;
}

// Utility routine--not a method.
// Preserve erasables.
void
ghost_moving_policy(entity *self, uint8_t pcnew, uint8_t vrnew) {
  uint8_t gc;

  // Check whether we previously saved an interfering character.
  // If so, re-display it at the saved coordinates.
  dot_interfering(self);

  // Defer the "save-under" logic until pcnew is even.
  if (pcnew & 1)
    return;

  // Are we stepping on anyone's toes (interfering)?
  // Note: interference is checked at the new coordinates.
  gc = get_grid_char(pcnew, vrnew);

  // A non-BL erasable character is said to be interfering.
  if ((gc != (uint8_t)' ') &&
    is_erasable_or_door(gc)) {
    if (self->igchr) {         // Did we already know about it?
      // Yes. Check for a new interference.
      if (self->igchr != gc) { // Interfering differently
        dot_interfering(self);
        self->igchr = gc;
        // Force even row#, wrt. interfering coordinates. TODO: legit?
        self->ivrown = vrnew & ~1;
        self->ipcoln = pcnew;
      }
      return;
    }

    // No, register interference details
    self->igchr = gc;
    // Force even row#, wrt. interfering coordinates. TODO: legit?
    self->ivrown = vrnew & ~1;
    self->ipcoln = pcnew;
    return;
  }

  dot_interfering(self);     // TODO: legit?
  self->igchr = 0;           // Clear interference record
}

// Utility routine--not a method.
void
collision_handle(entity *ghost_addr, uint8_t *pcol, uint8_t *vrow,
  uint8_t onproc) {

  // Defensive programming: make sure the entity at '*ghost_addr' is a ghost.
  if (((ghost_addr->inum < 1) || (ghost_addr->inum >= NENTITY)))
    crash_and_burn("collision-handle: not a ghost at '*ghost_addr'");

  if (fright_timer) {
    // The ghost at 'ghost_addr' dies--unless it is resurrecting.
    // Note: only Blinky resurrects outside of the pen.
    if (!ghost_addr->resurr) {
      dot_interfering(ghost_addr);
      ghost_addr->igchr = 0;   // Clear interference record

      ghost_addr->resurr = 50; // Ghost grounded for 50 clk cycles

      // Update the score based on PM's 'reward' field.
      if (PACMAN_ADDR->reward)
        PACMAN_ADDR->reward *= 2;
      else
        PACMAN_ADDR->reward = 2;
      update_score(100 * ((uint32_t)PACMAN_ADDR->reward));

      entity_reset_coords_and_dir(ghost_addr);

      // Ghost returned to the pen.
      if (onproc) {            // If the ghost just killed was ONPROC
        // Replace anticipated coordinates with the updated ones.
        *pcol = ghost_addr->pcoln;
        *vrow = ghost_addr->vrown;
      }
    }
    return;                    // We're done here
  }

  // PM dies
  pacman_dying_routine();
  update_lives();

  if (!lives)
    crash_and_burn("collision_handle: game over!");

  // If 'onproc' is zero, PM was ONPROC and we need to update
  // *pcol/*vrow to match PM's post mortem coordinates.
  if (!onproc) {
    *pcol = PACMAN_ADDR->pcoln;
    *vrow = PACMAN_ADDR->vrown;
    return;                    // We're done here
  }

  // A ghost is ONPROC and is responsible for PM's death.
  *pcol = ghost_addr->pcoln;
  *vrow = ghost_addr->vrown;
}

// Entity method.
void
entity_move(entity *self) {
  uint8_t pcnew, vrnew;
  int i;
  entity *ghost_addr = NULL;

  if (!self->inited) {
    entity_initial_display(self);
    self->inited = 1;
    return;
  }

  // 'cdir' validation.
  if (self->cdir > dir_blocked)
    crash_and_burn("entity_move: illegal current direction");

  // dir_blocked should only be in effect for PM, which
  // is an indication that some keyboard input is required.
  if ((self->cdir == dir_blocked) && (self->inum != 0))
    crash_and_burn("entity_move: ghost blocked!!!");

  self->cdir = self->inum ? ghost_dirselect(self) : pacman_dirselect(self);

  // Blank current position on screen.
  at_xy(X0 + self->pcoln, to_grid_space(self->vrown));
  dot_grid_char(' ');

  // Retrieve projected coordinates.
  entity_get_new_coordinates(self, &pcnew, &vrnew);

  if (self->inum)
    ghost_moving_policy(self, pcnew, vrnew);
  else
    pacman_moving_policy(self, pcnew, vrnew);

  // Update entity's coordinates fields.
  self->pcoln = pcnew;
  self->vrown = vrnew;

  // Collision handling.
  if (self->inum           // A ghost is ONPROC
    && is_pacman_stepped_on(self))
    ghost_addr = self;
  else {                   // PM is ONPROC
    // We have to check all possible ghosts' coordinates.
    for (i = 1; i < NENTITY; i++)
      if (is_pacman_stepped_on((entity *)(entvec[i]))) {
        ghost_addr = (entity *)(entvec[i]);
        break;
      }
  }

  // TODO: the following is kinda dubious...
  if (ghost_addr)
    collision_handle(ghost_addr, &pcnew, &vrnew, ghost_addr == self);

  // Display entity at new coordinates.
  at_xy(X0 + pcnew, to_grid_space(vrnew));
  entity_display(self);
}

uint32_t
serialno_getnext(void) {
  return serialno++;
}

// Entity constructor.
void *
entity_new(uint8_t hcvr, uint8_t hcpc, uint8_t vrow, uint8_t pcol,
  uint8_t cdir) {
  entity *ep;

  if (!(ep = calloc(sizeof(entity), 1)))
    crash_and_burn("entity_new: calloc returned NULL");

  // Initialize default valued fields.
  ep->strategy = (method)entity_move;
  ep->display = (method)entity_display;
  ep->pdir = dir_blocked;
  ep->idir = dir_unspec;

  // Initialize fields from arguments.
  ep->cdir = ep->dir0 = cdir;
  ep->pcoln = ep->pcol0 = pcol;
  ep->vrown = ep->vrow0 = vrow;
  ep->hcvrn = hcvr;
  ep->hcpcn = hcpc;

  // Intrinsics.
  ep->inum = serialno_getnext();
  return (void *)ep;
}

// -------------------------------------------------------------
// Ghost mode logic is time based but there's more to it than
// just time. When PM becomes "supercharged" the ghosts
// transition to the frightened state for some time.

uint32_t gm_seqno;
uint32_t gm_timer;

int32_t gm_sched[][3] = {
  //              L1      L2-4    L5+     seqno
  /* Scatter */ { 7,      7,      5    }, // 0
  /* Chase   */ { 20,     20,     20   }, // 1
  /* Scatter */ { 7,      7,      5    }, // 2
  /* Chase   */ { 20,     20,     20   }, // 3
  /* Scatter */ { 5,      5,      5    }, // 4
  /* Chase   */ { 20,     1033,   1037 }, // 5
  /* Scatter */ { 5,      1,      1    }, // 6
  /* Chase   */ { -1,     -1,     -1   }  // 6+ -> forever
};

// Returns a clock cycle count.
// TODO: this code should be under scrutiny.
int32_t
gm_timer_initval_get(uint8_t level, uint8_t seqno) {
  int32_t clk_cycles;
  int offset;

  // Defensive programming--enforce assumptions.
  if (!level)
    crash_and_burn("gm_timer_initval_get: level is zero");
  // TODO: seqno should also be checked for consistency.

  if (level == 1)
    offset = 0;
  else
    offset = level < 5 ? 1 : 2;

  clk_cycles = gm_sched[seqno][offset];
  if (clk_cycles == -1)
    return clk_cycles;

  return (clk_cycles * 1000) / CLKPERIOD;
}

uint8_t
gm_seqno_getnext(void) {
  // The sequence number is capped at 7.
  return gm_seqno < 6 ? 1 + gm_seqno : 7;
}

// Called after a context change (sequence number or game level).
ghostmode_t
gm_getnext(void) {
  int32_t ncycles;

  // Debugging code begins.
  // gm_timer_en = 0;
  // return mode_chase;
  // Debugging code ends.

  gm_timer_en = ncycles = gm_timer_initval_get(gamlev, gm_seqno);
  if (ncycles != (int32_t)-1) {
    gm_timer = ncycles;
    return gm_seqno & 1 ? mode_chase : mode_scatter;
  } 

  return mode_chase;
}

void
gm_prv_update(void) {
  if (gm_cur == mode_fright)
    return;
  gm_prv = gm_cur;
}

void
gm_switchto(ghostmode_t mode) {
  int i;

  if (mode == gm_cur)
    return;             // Current mode is not changing

  // If switching away from chase or scatter modes, signal
  // direction reversal request to all ghost instances.
  if (gm_cur != mode_fright) {
    for (i = 1; i < NENTITY; i++)
      ((entity *)entvec[i])->revflg = 1;
    bell();
  }

  gm_prv_update();
  gm_cur = mode;
}

void
super_enter(void) {
  // We might want to return immediately depending on 'gamlev'
  if (gm_cur == mode_fright) {      // Already frightened
    fright_timer = SUPER_CLKCYCLES; // Be kind, reset the timer!
    return;
  }

  gm_prv_update();
  gm_cur = mode_fright;
  gm_timer_en = 0;                  // Suspend gm_timer
  fright_timer = SUPER_CLKCYCLES;   // Enable the 'fright' timer
}

void
super_leave(void) {
  PACMAN_ADDR->reward = 0;          // Reset ghost kill counter
  gm_switchto(gm_prv);
  gm_timer_en = -1;                 // Re-enable gm_timer
}

// -------------------------------------------------------------
// Reset all entities coords/dir and set 'inited' to FALSE.
// Also clear 'fright_timer' and PM's 'reward' field.
// Reset the PRNG's seed to a fixed value, as per the gospel.

void
level_entry_inits(void) {
  entity *ep;
  int i;

  entity_reset_coords_and_dir(PACMAN_ADDR);
  PACMAN_ADDR->inited = 0;
  PACMAN_ADDR->reward = 0;

  for (i = 1; i < NENTITY; i++) {
    ep = ((entity *)entvec[i]);
    entity_reset_coords_and_dir(ep);
    ep->inited = 0;
  }

  seed = 23741;

  // Ghost mode level entry initializations.
  fright_timer = 0;
  gm_seqno = 0;
  gm_cur = gm_getnext();
  gm_prv = mode_unspec;
}

// -------------------------------------------------------------
// Entry point here.

void
_main(void) {
  entity *ep;
  int i;

  for (;;) {
    if (!nremitem) {                // If nremitem is 0, start new level
      dot_initial_grid();
      update_level();
      level_entry_inits();
      continue;
    }

    // Ghost mode handling.
    if (gm_cur == mode_fright) {
      if (fright_timer) {           // Continue w/ frightened ghosts
        fright_timer--;
        update_suptim();
      }
      else
        super_leave();
    }
    else {
      if (gm_timer_en) {
        if (gm_timer)
          gm_timer--;               // Ghost mode unchanged
        else {
          gm_seqno = gm_seqno_getnext();
          gm_switchto(gm_getnext());
        }
      }
    }

    // Regular entity scheduling.
    for (i = 0; i < NENTITY; i++) {
      ep = (entity *)entvec[i];
      ep->strategy(ep);
    }

    ms(CLKPERIOD);
  }
}

int
main() {
  initialize();
#ifndef FORCE_CURSES                // Skip page() if using curses
  page();
#endif
  dot_init_sitrep();                // Initial scoreboard

  _main();                          // No return

  return 0;
}

