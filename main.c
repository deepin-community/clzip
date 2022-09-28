/* Clzip - LZMA lossless data compressor
   Copyright (C) 2010-2021 Antonio Diaz Diaz.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
/*
   Exit status: 0 for a normal exit, 1 for environmental problems
   (file not found, invalid flags, I/O errors, etc), 2 to indicate a
   corrupt or invalid input file, 3 for an internal consistency error
   (eg, bug) which caused clzip to panic.
*/

#define _FILE_OFFSET_BITS 64

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <utime.h>
#include <sys/stat.h>
#if defined(__MSVCRT__) || defined(__OS2__) || defined(__DJGPP__)
#include <io.h>
#if defined(__MSVCRT__)
#define fchmod(x,y) 0
#define fchown(x,y,z) 0
#define strtoull strtoul
#define SIGHUP SIGTERM
#define S_ISSOCK(x) 0
#ifndef S_IRGRP
#define S_IRGRP 0
#define S_IWGRP 0
#define S_IROTH 0
#define S_IWOTH 0
#endif
#endif
#if defined(__DJGPP__)
#define S_ISSOCK(x) 0
#define S_ISVTX 0
#endif
#endif

#include "carg_parser.h"
#include "lzip.h"
#include "decoder.h"
#include "encoder_base.h"
#include "encoder.h"
#include "fast_encoder.h"

#ifndef O_BINARY
#define O_BINARY 0
#endif

#if CHAR_BIT != 8
#error "Environments where CHAR_BIT != 8 are not supported."
#endif

int verbosity = 0;

static const char * const program_name = "clzip";
static const char * const program_year = "2021";
static const char * invocation_name = "clzip";		/* default value */

static const struct { const char * from; const char * to; } known_extensions[] = {
  { ".lz",  ""     },
  { ".tlz", ".tar" },
  { 0,      0      } };

struct Lzma_options
  {
  int dictionary_size;		/* 4 KiB .. 512 MiB */
  int match_len_limit;		/* 5 .. 273 */
  };

enum Mode { m_compress, m_decompress, m_list, m_test };

/* Variables used in signal handler context.
   They are not declared volatile because the handler never returns. */
static char * output_filename = 0;
static int outfd = -1;
static bool delete_output_on_interrupt = false;


static void show_help( void )
  {
  printf( "Clzip is a C language version of lzip, fully compatible with lzip 1.4 or\n"
          "newer. As clzip is written in C, it may be easier to integrate in\n"
          "applications like package managers, embedded devices, or systems lacking a\n"
          "C++ compiler.\n"
          "\nLzip is a lossless data compressor with a user interface similar to the one\n"
          "of gzip or bzip2. Lzip uses a simplified form of the 'Lempel-Ziv-Markov\n"
          "chain-Algorithm' (LZMA) stream format, chosen to maximize safety and\n"
          "interoperability. Lzip can compress about as fast as gzip (lzip -0) or\n"
          "compress most files more than bzip2 (lzip -9). Decompression speed is\n"
          "intermediate between gzip and bzip2. Lzip is better than gzip and bzip2 from\n"
          "a data recovery perspective. Lzip has been designed, written, and tested\n"
          "with great care to replace gzip and bzip2 as the standard general-purpose\n"
          "compressed format for unix-like systems.\n"
          "\nUsage: %s [options] [files]\n", invocation_name );
  printf( "\nOptions:\n"
          "  -h, --help                     display this help and exit\n"
          "  -V, --version                  output version information and exit\n"
          "  -a, --trailing-error           exit with error status if trailing data\n"
          "  -b, --member-size=<bytes>      set member size limit in bytes\n"
          "  -c, --stdout                   write to standard output, keep input files\n"
          "  -d, --decompress               decompress\n"
          "  -f, --force                    overwrite existing output files\n"
          "  -F, --recompress               force re-compression of compressed files\n"
          "  -k, --keep                     keep (don't delete) input files\n"
          "  -l, --list                     print (un)compressed file sizes\n"
          "  -m, --match-length=<bytes>     set match length limit in bytes [36]\n"
          "  -o, --output=<file>            write to <file>, keep input files\n"
          "  -q, --quiet                    suppress all messages\n"
          "  -s, --dictionary-size=<bytes>  set dictionary size limit in bytes [8 MiB]\n"
          "  -S, --volume-size=<bytes>      set volume size limit in bytes\n"
          "  -t, --test                     test compressed file integrity\n"
          "  -v, --verbose                  be verbose (a 2nd -v gives more)\n"
          "  -0 .. -9                       set compression level [default 6]\n"
          "      --fast                     alias for -0\n"
          "      --best                     alias for -9\n"
          "      --loose-trailing           allow trailing data seeming corrupt header\n"
          "\nIf no file names are given, or if a file is '-', clzip compresses or\n"
          "decompresses from standard input to standard output.\n"
          "Numbers may be followed by a multiplier: k = kB = 10^3 = 1000,\n"
          "Ki = KiB = 2^10 = 1024, M = 10^6, Mi = 2^20, G = 10^9, Gi = 2^30, etc...\n"
          "Dictionary sizes 12 to 29 are interpreted as powers of two, meaning 2^12\n"
          "to 2^29 bytes.\n"
          "\nThe bidimensional parameter space of LZMA can't be mapped to a linear\n"
          "scale optimal for all files. If your files are large, very repetitive,\n"
          "etc, you may need to use the options --dictionary-size and --match-length\n"
          "directly to achieve optimal performance.\n"
          "\nTo extract all the files from archive 'foo.tar.lz', use the commands\n"
          "'tar -xf foo.tar.lz' or 'clzip -cd foo.tar.lz | tar -xf -'.\n"
          "\nExit status: 0 for a normal exit, 1 for environmental problems (file\n"
          "not found, invalid flags, I/O errors, etc), 2 to indicate a corrupt or\n"
          "invalid input file, 3 for an internal consistency error (eg, bug) which\n"
          "caused clzip to panic.\n"
          "\nThe ideas embodied in clzip are due to (at least) the following people:\n"
          "Abraham Lempel and Jacob Ziv (for the LZ algorithm), Andrey Markov (for the\n"
          "definition of Markov chains), G.N.N. Martin (for the definition of range\n"
          "encoding), Igor Pavlov (for putting all the above together in LZMA), and\n"
          "Julian Seward (for bzip2's CLI).\n"
          "\nReport bugs to lzip-bug@nongnu.org\n"
          "Clzip home page: http://www.nongnu.org/lzip/clzip.html\n" );
  }


static void show_version( void )
  {
  printf( "%s %s\n", program_name, PROGVERSION );
  printf( "Copyright (C) %s Antonio Diaz Diaz.\n", program_year );
  printf( "License GPLv2+: GNU GPL version 2 or later <http://gnu.org/licenses/gpl.html>\n"
          "This is free software: you are free to change and redistribute it.\n"
          "There is NO WARRANTY, to the extent permitted by law.\n" );
  }


/* assure at least a minimum size for buffer 'buf' */
void * resize_buffer( void * buf, const unsigned min_size )
  {
  if( buf ) buf = realloc( buf, min_size );
  else buf = malloc( min_size );
  if( !buf ) { show_error( mem_msg, 0, false ); cleanup_and_fail( 1 ); }
  return buf;
  }


struct Pretty_print
  {
  const char * name;
  char * padded_name;
  const char * stdin_name;
  unsigned longest_name;
  bool first_post;
  };

static void Pp_init( struct Pretty_print * const pp,
                     const char * const filenames[], const int num_filenames )
  {
  unsigned stdin_name_len;
  int i;
  pp->name = 0;
  pp->padded_name = 0;
  pp->stdin_name = "(stdin)";
  pp->longest_name = 0;
  pp->first_post = false;

  if( verbosity <= 0 ) return;
  stdin_name_len = strlen( pp->stdin_name );
  for( i = 0; i < num_filenames; ++i )
    {
    const char * const s = filenames[i];
    const unsigned len = (strcmp( s, "-" ) == 0) ? stdin_name_len : strlen( s );
    if( pp->longest_name < len ) pp->longest_name = len;
    }
  if( pp->longest_name == 0 ) pp->longest_name = stdin_name_len;
  }

static void Pp_set_name( struct Pretty_print * const pp,
                         const char * const filename )
  {
  unsigned name_len, padded_name_len, i = 0;

  if( filename && filename[0] && strcmp( filename, "-" ) != 0 )
    pp->name = filename;
  else pp->name = pp->stdin_name;
  name_len = strlen( pp->name );
  padded_name_len = max( name_len, pp->longest_name ) + 4;
  pp->padded_name = resize_buffer( pp->padded_name, padded_name_len + 1 );
  while( i < 2 ) pp->padded_name[i++] = ' ';
  while( i < name_len + 2 ) { pp->padded_name[i] = pp->name[i-2]; ++i; }
  pp->padded_name[i++] = ':';
  while( i < padded_name_len ) pp->padded_name[i++] = ' ';
  pp->padded_name[i] = 0;
  pp->first_post = true;
  }

static void Pp_reset( struct Pretty_print * const pp )
  { if( pp->name && pp->name[0] ) pp->first_post = true; }

void Pp_show_msg( struct Pretty_print * const pp, const char * const msg )
  {
  if( verbosity >= 0 )
    {
    if( pp->first_post )
      {
      pp->first_post = false;
      fputs( pp->padded_name, stderr );
      if( !msg ) fflush( stderr );
      }
    if( msg ) fprintf( stderr, "%s\n", msg );
    }
  }


const char * bad_version( const unsigned version )
  {
  static char buf[80];
  snprintf( buf, sizeof buf, "Version %u member format not supported.",
            version );
  return buf;
  }


const char * format_ds( const unsigned dictionary_size )
  {
  enum { bufsize = 16, factor = 1024 };
  static char buf[bufsize];
  const char * const prefix[8] =
    { "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi", "Yi" };
  const char * p = "";
  const char * np = "  ";
  unsigned num = dictionary_size;
  bool exact = ( num % factor == 0 );

  int i; for( i = 0; i < 8 && ( num > 9999 || ( exact && num >= factor ) ); ++i )
    { num /= factor; if( num % factor != 0 ) exact = false;
      p = prefix[i]; np = ""; }
  snprintf( buf, bufsize, "%s%4u %sB", np, num, p );
  return buf;
  }


void show_header( const unsigned dictionary_size )
  {
  fprintf( stderr, "dict %s, ", format_ds( dictionary_size ) );
  }


static unsigned long long getnum( const char * const ptr,
                                  const unsigned long long llimit,
                                  const unsigned long long ulimit )
  {
  unsigned long long result;
  char * tail;
  errno = 0;
  result = strtoull( ptr, &tail, 0 );
  if( tail == ptr )
    {
    show_error( "Bad or missing numerical argument.", 0, true );
    exit( 1 );
    }

  if( !errno && tail[0] )
    {
    const unsigned factor = ( tail[1] == 'i' ) ? 1024 : 1000;
    int exponent = 0;				/* 0 = bad multiplier */
    int i;
    switch( tail[0] )
      {
      case 'Y': exponent = 8; break;
      case 'Z': exponent = 7; break;
      case 'E': exponent = 6; break;
      case 'P': exponent = 5; break;
      case 'T': exponent = 4; break;
      case 'G': exponent = 3; break;
      case 'M': exponent = 2; break;
      case 'K': if( factor == 1024 ) exponent = 1; break;
      case 'k': if( factor == 1000 ) exponent = 1; break;
      }
    if( exponent <= 0 )
      {
      show_error( "Bad multiplier in numerical argument.", 0, true );
      exit( 1 );
      }
    for( i = 0; i < exponent; ++i )
      {
      if( ulimit / factor >= result ) result *= factor;
      else { errno = ERANGE; break; }
      }
    }
  if( !errno && ( result < llimit || result > ulimit ) ) errno = ERANGE;
  if( errno )
    {
    show_error( "Numerical argument out of limits.", 0, false );
    exit( 1 );
    }
  return result;
  }


static int get_dict_size( const char * const arg )
  {
  char * tail;
  const long bits = strtol( arg, &tail, 0 );
  if( bits >= min_dictionary_bits &&
      bits <= max_dictionary_bits && *tail == 0 )
    return 1 << bits;
  return getnum( arg, min_dictionary_size, max_dictionary_size );
  }


static void set_mode( enum Mode * const program_modep, const enum Mode new_mode )
  {
  if( *program_modep != m_compress && *program_modep != new_mode )
    {
    show_error( "Only one operation can be specified.", 0, true );
    exit( 1 );
    }
  *program_modep = new_mode;
  }


static int extension_index( const char * const name )
  {
  int eindex;
  for( eindex = 0; known_extensions[eindex].from; ++eindex )
    {
    const char * const ext = known_extensions[eindex].from;
    const unsigned name_len = strlen( name );
    const unsigned ext_len = strlen( ext );
    if( name_len > ext_len &&
        strncmp( name + name_len - ext_len, ext, ext_len ) == 0 )
      return eindex;
    }
  return -1;
  }


static void set_c_outname( const char * const name, const bool filenames_given,
                           const bool force_ext, const bool multifile )
  {
  /* zupdate < 1.9 depends on lzip adding the extension '.lz' to name when
     reading from standard input. */
  output_filename = resize_buffer( output_filename, strlen( name ) + 5 +
                                   strlen( known_extensions[0].from ) + 1 );
  strcpy( output_filename, name );
  if( multifile ) strcat( output_filename, "00001" );
  if( force_ext || multifile ||
      ( !filenames_given && extension_index( output_filename ) < 0 ) )
    strcat( output_filename, known_extensions[0].from );
  }


static void set_d_outname( const char * const name, const int eindex )
  {
  const unsigned name_len = strlen( name );
  if( eindex >= 0 )
    {
    const char * const from = known_extensions[eindex].from;
    const unsigned from_len = strlen( from );
    if( name_len > from_len )
      {
      output_filename = resize_buffer( output_filename, name_len +
                                       strlen( known_extensions[eindex].to ) + 1 );
      strcpy( output_filename, name );
      strcpy( output_filename + name_len - from_len, known_extensions[eindex].to );
      return;
      }
    }
  output_filename = resize_buffer( output_filename, name_len + 4 + 1 );
  strcpy( output_filename, name );
  strcat( output_filename, ".out" );
  if( verbosity >= 1 )
    fprintf( stderr, "%s: Can't guess original name for '%s' -- using '%s'\n",
             program_name, name, output_filename );
  }


int open_instream( const char * const name, struct stat * const in_statsp,
                   const bool one_to_one, const bool reg_only )
  {
  int infd = open( name, O_RDONLY | O_BINARY );
  if( infd < 0 )
    show_file_error( name, "Can't open input file", errno );
  else
    {
    const int i = fstat( infd, in_statsp );
    const mode_t mode = in_statsp->st_mode;
    const bool can_read = ( i == 0 && !reg_only &&
                            ( S_ISBLK( mode ) || S_ISCHR( mode ) ||
                              S_ISFIFO( mode ) || S_ISSOCK( mode ) ) );
    if( i != 0 || ( !S_ISREG( mode ) && ( !can_read || one_to_one ) ) )
      {
      if( verbosity >= 0 )
        fprintf( stderr, "%s: Input file '%s' is not a regular file%s.\n",
                 program_name, name, ( can_read && one_to_one ) ?
                 ",\n       and neither '-c' nor '-o' were specified" : "" );
      close( infd );
      infd = -1;
      }
    }
  return infd;
  }


static int open_instream2( const char * const name, struct stat * const in_statsp,
                           const enum Mode program_mode, const int eindex,
                           const bool one_to_one, const bool recompress )
  {
  if( program_mode == m_compress && !recompress && eindex >= 0 )
    {
    if( verbosity >= 0 )
      fprintf( stderr, "%s: Input file '%s' already has '%s' suffix.\n",
               program_name, name, known_extensions[eindex].from );
    return -1;
    }
  return open_instream( name, in_statsp, one_to_one, false );
  }


static bool open_outstream( const bool force, const bool protect )
  {
  const mode_t usr_rw = S_IRUSR | S_IWUSR;
  const mode_t all_rw = usr_rw | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH;
  const mode_t outfd_mode = protect ? usr_rw : all_rw;
  int flags = O_CREAT | O_WRONLY | O_BINARY;
  if( force ) flags |= O_TRUNC; else flags |= O_EXCL;

  outfd = open( output_filename, flags, outfd_mode );
  if( outfd >= 0 ) delete_output_on_interrupt = true;
  else if( verbosity >= 0 )
    {
    if( errno == EEXIST )
      fprintf( stderr, "%s: Output file '%s' already exists, skipping.\n",
               program_name, output_filename );
    else
      fprintf( stderr, "%s: Can't create output file '%s': %s\n",
               program_name, output_filename, strerror( errno ) );
    }
  return ( outfd >= 0 );
  }


static void set_signals( void (*action)(int) )
  {
  signal( SIGHUP, action );
  signal( SIGINT, action );
  signal( SIGTERM, action );
  }


void cleanup_and_fail( const int retval )
  {
  set_signals( SIG_IGN );			/* ignore signals */
  if( delete_output_on_interrupt )
    {
    delete_output_on_interrupt = false;
    if( verbosity >= 0 )
      fprintf( stderr, "%s: Deleting output file '%s', if it exists.\n",
               program_name, output_filename );
    if( outfd >= 0 ) { close( outfd ); outfd = -1; }
    if( remove( output_filename ) != 0 && errno != ENOENT )
      show_error( "WARNING: deletion of output file (apparently) failed.", 0, false );
    }
  exit( retval );
  }


static void signal_handler( int sig )
  {
  if( sig ) {}				/* keep compiler happy */
  show_error( "Control-C or similar caught, quitting.", 0, false );
  cleanup_and_fail( 1 );
  }


static bool check_tty_in( const char * const input_filename, const int infd,
                          const enum Mode program_mode, int * const retval )
  {
  if( ( program_mode == m_decompress || program_mode == m_test ) &&
      isatty( infd ) )				/* for example /dev/tty */
    { show_file_error( input_filename,
                       "I won't read compressed data from a terminal.", 0 );
      close( infd ); set_retval( retval, 1 );
      if( program_mode != m_test ) cleanup_and_fail( *retval );
      return false; }
  return true;
  }

static bool check_tty_out( const enum Mode program_mode )
  {
  if( program_mode == m_compress && isatty( outfd ) )
    { show_file_error( output_filename[0] ?
                       output_filename : "(stdout)",
                       "I won't write compressed data to a terminal.", 0 );
      return false; }
  return true;
  }


/* Set permissions, owner, and times. */
static void close_and_set_permissions( const struct stat * const in_statsp )
  {
  bool warning = false;
  if( in_statsp )
    {
    const mode_t mode = in_statsp->st_mode;
    /* fchown will in many cases return with EPERM, which can be safely ignored. */
    if( fchown( outfd, in_statsp->st_uid, in_statsp->st_gid ) == 0 )
      { if( fchmod( outfd, mode ) != 0 ) warning = true; }
    else
      if( errno != EPERM ||
          fchmod( outfd, mode & ~( S_ISUID | S_ISGID | S_ISVTX ) ) != 0 )
        warning = true;
    }
  if( close( outfd ) != 0 )
    {
    show_error( "Error closing output file", errno, false );
    cleanup_and_fail( 1 );
    }
  outfd = -1;
  delete_output_on_interrupt = false;
  if( in_statsp )
    {
    struct utimbuf t;
    t.actime = in_statsp->st_atime;
    t.modtime = in_statsp->st_mtime;
    if( utime( output_filename, &t ) != 0 ) warning = true;
    }
  if( warning && verbosity >= 1 )
    show_error( "Can't change output file attributes.", 0, false );
  }


static bool next_filename( void )
  {
  const unsigned name_len = strlen( output_filename );
  const unsigned ext_len = strlen( known_extensions[0].from );
  int i, j;
  if( name_len >= ext_len + 5 )				/* "*00001.lz" */
    for( i = name_len - ext_len - 1, j = 0; j < 5; --i, ++j )
      {
      if( output_filename[i] < '9' ) { ++output_filename[i]; return true; }
      else output_filename[i] = '0';
      }
  return false;
  }


struct Poly_encoder
  {
  struct LZ_encoder_base * eb;
  struct LZ_encoder * e;
  struct FLZ_encoder * fe;
  };


static int compress( const unsigned long long cfile_size,
                     const unsigned long long member_size,
                     const unsigned long long volume_size, const int infd,
                     const struct Lzma_options * const encoder_options,
                     struct Pretty_print * const pp,
                     const struct stat * const in_statsp, const bool zero )
  {
  unsigned long long in_size = 0, out_size = 0, partial_volume_size = 0;
  int retval = 0;
  struct Poly_encoder encoder = { 0, 0, 0 };	/* polymorphic encoder */
  if( verbosity >= 1 ) Pp_show_msg( pp, 0 );

  {
  bool error = false;
  if( zero )
    {
    encoder.fe = (struct FLZ_encoder *)malloc( sizeof *encoder.fe );
    if( !encoder.fe || !FLZe_init( encoder.fe, infd, outfd ) ) error = true;
    else encoder.eb = &encoder.fe->eb;
    }
  else
    {
    Lzip_header header;
    if( Lh_set_dictionary_size( header, encoder_options->dictionary_size ) &&
        encoder_options->match_len_limit >= min_match_len_limit &&
        encoder_options->match_len_limit <= max_match_len )
      encoder.e = (struct LZ_encoder *)malloc( sizeof *encoder.e );
    else internal_error( "invalid argument to encoder." );
    if( !encoder.e || !LZe_init( encoder.e, Lh_get_dictionary_size( header ),
                                 encoder_options->match_len_limit, infd, outfd ) )
      error = true;
    else encoder.eb = &encoder.e->eb;
    }
  if( error )
    {
    Pp_show_msg( pp, "Not enough memory. Try a smaller dictionary size." );
    return 1;
    }
  }

  while( true )			/* encode one member per iteration */
    {
    const unsigned long long size = ( volume_size > 0 ) ?
      min( member_size, volume_size - partial_volume_size ) : member_size;
    show_cprogress( cfile_size, in_size, &encoder.eb->mb, pp );	/* init */
    if( ( zero && !FLZe_encode_member( encoder.fe, size ) ) ||
        ( !zero && !LZe_encode_member( encoder.e, size ) ) )
      { Pp_show_msg( pp, "Encoder error." ); retval = 1; break; }
    in_size += Mb_data_position( &encoder.eb->mb );
    out_size += Re_member_position( &encoder.eb->renc );
    if( Mb_data_finished( &encoder.eb->mb ) ) break;
    if( volume_size > 0 )
      {
      partial_volume_size += Re_member_position( &encoder.eb->renc );
      if( partial_volume_size >= volume_size - min_dictionary_size )
        {
        partial_volume_size = 0;
        if( delete_output_on_interrupt )
          {
          close_and_set_permissions( in_statsp );
          if( !next_filename() )
            { Pp_show_msg( pp, "Too many volume files." ); retval = 1; break; }
          if( !open_outstream( true, in_statsp ) ) { retval = 1; break; }
          }
        }
      }
    if( zero ) FLZe_reset( encoder.fe ); else LZe_reset( encoder.e );
    }

  if( retval == 0 && verbosity >= 1 )
    {
    if( in_size == 0 || out_size == 0 )
      fputs( " no data compressed.\n", stderr );
    else
      fprintf( stderr, "%6.3f:1, %5.2f%% ratio, %5.2f%% saved, "
                       "%llu in, %llu out.\n",
               (double)in_size / out_size,
               ( 100.0 * out_size ) / in_size,
               100.0 - ( ( 100.0 * out_size ) / in_size ),
               in_size, out_size );
    }
  LZeb_free( encoder.eb );
  if( zero ) free( encoder.fe ); else free( encoder.e );
  return retval;
  }


static unsigned char xdigit( const unsigned value )
  {
  if( value <= 9 ) return '0' + value;
  if( value <= 15 ) return 'A' + value - 10;
  return 0;
  }


static bool show_trailing_data( const uint8_t * const data, const int size,
                                struct Pretty_print * const pp, const bool all,
                                const int ignore_trailing )	/* -1 = show */
  {
  if( verbosity >= 4 || ignore_trailing <= 0 )
    {
    int i;
    char buf[80];
    unsigned len = max( 0, snprintf( buf, sizeof buf, "%strailing data = ",
                                     all ? "" : "first bytes of " ) );
    for( i = 0; i < size && len + 2 < sizeof buf; ++i )
      {
      buf[len++] = xdigit( data[i] >> 4 );
      buf[len++] = xdigit( data[i] & 0x0F );
      buf[len++] = ' ';
      }
    if( len < sizeof buf ) buf[len++] = '\'';
    for( i = 0; i < size && len < sizeof buf; ++i )
      { if( isprint( data[i] ) ) buf[len++] = data[i]; else buf[len++] = '.'; }
    if( len < sizeof buf ) buf[len++] = '\'';
    if( len < sizeof buf ) buf[len] = 0; else buf[sizeof buf - 1] = 0;
    Pp_show_msg( pp, buf );
    if( ignore_trailing == 0 ) show_file_error( pp->name, trailing_msg, 0 );
    }
  return ( ignore_trailing > 0 );
  }


static int decompress( const unsigned long long cfile_size, const int infd,
                struct Pretty_print * const pp, const bool ignore_trailing,
                const bool loose_trailing, const bool testing )
  {
  unsigned long long partial_file_pos = 0;
  struct Range_decoder rdec;
  int retval = 0;
  bool first_member;
  if( !Rd_init( &rdec, infd ) )
    { show_error( mem_msg, 0, false ); cleanup_and_fail( 1 ); }

  for( first_member = true; ; first_member = false )
    {
    int result, size;
    unsigned dictionary_size;
    Lzip_header header;
    struct LZ_decoder decoder;
    Rd_reset_member_position( &rdec );
    size = Rd_read_data( &rdec, header, Lh_size );
    if( Rd_finished( &rdec ) )			/* End Of File */
      {
      if( first_member )
        { show_file_error( pp->name, "File ends unexpectedly at member header.", 0 );
          retval = 2; }
      else if( Lh_verify_prefix( header, size ) )
        { Pp_show_msg( pp, "Truncated header in multimember file." );
          show_trailing_data( header, size, pp, true, -1 );
          retval = 2; }
      else if( size > 0 && !show_trailing_data( header, size, pp,
                                                true, ignore_trailing ) )
        retval = 2;
      break;
      }
    if( !Lh_verify_magic( header ) )
      {
      if( first_member )
        { show_file_error( pp->name, bad_magic_msg, 0 ); retval = 2; }
      else if( !loose_trailing && Lh_verify_corrupt( header ) )
        { Pp_show_msg( pp, corrupt_mm_msg );
          show_trailing_data( header, size, pp, false, -1 );
          retval = 2; }
      else if( !show_trailing_data( header, size, pp, false, ignore_trailing ) )
        retval = 2;
      break;
      }
    if( !Lh_verify_version( header ) )
      { Pp_show_msg( pp, bad_version( Lh_version( header ) ) );
        retval = 2; break; }
    dictionary_size = Lh_get_dictionary_size( header );
    if( !isvalid_ds( dictionary_size ) )
      { Pp_show_msg( pp, bad_dict_msg ); retval = 2; break; }

    if( verbosity >= 2 || ( verbosity == 1 && first_member ) )
      Pp_show_msg( pp, 0 );

    if( !LZd_init( &decoder, &rdec, dictionary_size, outfd ) )
      { Pp_show_msg( pp, mem_msg ); retval = 1; break; }
    show_dprogress( cfile_size, partial_file_pos, &rdec, pp );	/* init */
    result = LZd_decode_member( &decoder, pp );
    partial_file_pos += Rd_member_position( &rdec );
    LZd_free( &decoder );
    if( result != 0 )
      {
      if( verbosity >= 0 && result <= 2 )
        {
        Pp_show_msg( pp, 0 );
        fprintf( stderr, "%s at pos %llu\n", ( result == 2 ) ?
                 "File ends unexpectedly" : "Decoder error",
                 partial_file_pos );
        }
      retval = 2; break;
      }
    if( verbosity >= 2 )
      { fputs( testing ? "ok\n" : "done\n", stderr ); Pp_reset( pp ); }
    }
  Rd_free( &rdec );
  if( verbosity == 1 && retval == 0 )
    fputs( testing ? "ok\n" : "done\n", stderr );
  return retval;
  }


void show_error( const char * const msg, const int errcode, const bool help )
  {
  if( verbosity < 0 ) return;
  if( msg && msg[0] )
    fprintf( stderr, "%s: %s%s%s\n", program_name, msg,
             ( errcode > 0 ) ? ": " : "",
             ( errcode > 0 ) ? strerror( errcode ) : "" );
  if( help )
    fprintf( stderr, "Try '%s --help' for more information.\n",
             invocation_name );
  }


void show_file_error( const char * const filename, const char * const msg,
                      const int errcode )
  {
  if( verbosity >= 0 )
    fprintf( stderr, "%s: %s: %s%s%s\n", program_name, filename, msg,
             ( errcode > 0 ) ? ": " : "",
             ( errcode > 0 ) ? strerror( errcode ) : "" );
  }


void internal_error( const char * const msg )
  {
  if( verbosity >= 0 )
    fprintf( stderr, "%s: internal error: %s\n", program_name, msg );
  exit( 3 );
  }


void show_cprogress( const unsigned long long cfile_size,
                     const unsigned long long partial_size,
                     const struct Matchfinder_base * const m,
                     struct Pretty_print * const p )
  {
  static unsigned long long csize = 0;		/* file_size / 100 */
  static unsigned long long psize = 0;
  static const struct Matchfinder_base * mb = 0;
  static struct Pretty_print * pp = 0;
  static bool enabled = true;

  if( !enabled ) return;
  if( p )					/* initialize static vars */
    {
    if( verbosity < 2 || !isatty( STDERR_FILENO ) ) { enabled = false; return; }
    csize = cfile_size; psize = partial_size; mb = m; pp = p;
    }
  if( mb && pp )
    {
    const unsigned long long pos = psize + Mb_data_position( mb );
    if( csize > 0 )
      fprintf( stderr, "%4llu%%  %.1f MB\r", pos / csize, pos / 1000000.0 );
    else
      fprintf( stderr, "  %.1f MB\r", pos / 1000000.0 );
    Pp_reset( pp ); Pp_show_msg( pp, 0 );	/* restore cursor position */
    }
  }


void show_dprogress( const unsigned long long cfile_size,
                     const unsigned long long partial_size,
                     const struct Range_decoder * const d,
                     struct Pretty_print * const p )
  {
  static unsigned long long csize = 0;		/* file_size / 100 */
  static unsigned long long psize = 0;
  static const struct Range_decoder * rdec = 0;
  static struct Pretty_print * pp = 0;
  static int counter = 0;
  static bool enabled = true;

  if( !enabled ) return;
  if( p )					/* initialize static vars */
    {
    if( verbosity < 2 || !isatty( STDERR_FILENO ) ) { enabled = false; return; }
    csize = cfile_size; psize = partial_size; rdec = d; pp = p; counter = 0;
    }
  if( rdec && pp && --counter <= 0 )
    {
    const unsigned long long pos = psize + Rd_member_position( rdec );
    counter = 7;		/* update display every 114688 bytes */
    if( csize > 0 )
      fprintf( stderr, "%4llu%%  %.1f MB\r", pos / csize, pos / 1000000.0 );
    else
      fprintf( stderr, "  %.1f MB\r", pos / 1000000.0 );
    Pp_reset( pp ); Pp_show_msg( pp, 0 );	/* restore cursor position */
    }
  }


int main( const int argc, const char * const argv[] )
  {
  /* Mapping from gzip/bzip2 style 1..9 compression modes
     to the corresponding LZMA compression modes. */
  const struct Lzma_options option_mapping[] =
    {
    { 1 << 16,  16 },		/* -0 */
    { 1 << 20,   5 },		/* -1 */
    { 3 << 19,   6 },		/* -2 */
    { 1 << 21,   8 },		/* -3 */
    { 3 << 20,  12 },		/* -4 */
    { 1 << 22,  20 },		/* -5 */
    { 1 << 23,  36 },		/* -6 */
    { 1 << 24,  68 },		/* -7 */
    { 3 << 23, 132 },		/* -8 */
    { 1 << 25, 273 } };		/* -9 */
  struct Lzma_options encoder_options = option_mapping[6];  /* default = "-6" */
  const unsigned long long max_member_size = 0x0008000000000000ULL; /* 2 PiB */
  const unsigned long long max_volume_size = 0x4000000000000000ULL; /* 4 EiB */
  unsigned long long member_size = max_member_size;
  unsigned long long volume_size = 0;
  const char * default_output_filename = "";
  static struct Arg_parser parser;	/* static because valgrind complains */
  static struct Pretty_print pp;	/* and memory management in C sucks */
  static const char ** filenames = 0;
  int num_filenames = 0;
  enum Mode program_mode = m_compress;
  int argind = 0;
  int failed_tests = 0;
  int retval = 0;
  int i;
  bool filenames_given = false;
  bool force = false;
  bool ignore_trailing = true;
  bool keep_input_files = false;
  bool loose_trailing = false;
  bool recompress = false;
  bool stdin_used = false;
  bool to_stdout = false;
  bool zero = false;

  enum { opt_lt = 256 };
  const struct ap_Option options[] =
    {
    { '0', "fast",              ap_no  },
    { '1', 0,                   ap_no  },
    { '2', 0,                   ap_no  },
    { '3', 0,                   ap_no  },
    { '4', 0,                   ap_no  },
    { '5', 0,                   ap_no  },
    { '6', 0,                   ap_no  },
    { '7', 0,                   ap_no  },
    { '8', 0,                   ap_no  },
    { '9', "best",              ap_no  },
    { 'a', "trailing-error",    ap_no  },
    { 'b', "member-size",       ap_yes },
    { 'c', "stdout",            ap_no  },
    { 'd', "decompress",        ap_no  },
    { 'f', "force",             ap_no  },
    { 'F', "recompress",        ap_no  },
    { 'h', "help",              ap_no  },
    { 'k', "keep",              ap_no  },
    { 'l', "list",              ap_no  },
    { 'm', "match-length",      ap_yes },
    { 'n', "threads",           ap_yes },
    { 'o', "output",            ap_yes },
    { 'q', "quiet",             ap_no  },
    { 's', "dictionary-size",   ap_yes },
    { 'S', "volume-size",       ap_yes },
    { 't', "test",              ap_no  },
    { 'v', "verbose",           ap_no  },
    { 'V', "version",           ap_no  },
    { opt_lt, "loose-trailing", ap_no  },
    {  0, 0,                    ap_no  } };

  if( argc > 0 ) invocation_name = argv[0];
  CRC32_init();

  if( !ap_init( &parser, argc, argv, options, 0 ) )
    { show_error( mem_msg, 0, false ); return 1; }
  if( ap_error( &parser ) )				/* bad option */
    { show_error( ap_error( &parser ), 0, true ); return 1; }

  for( ; argind < ap_arguments( &parser ); ++argind )
    {
    const int code = ap_code( &parser, argind );
    const char * const arg = ap_argument( &parser, argind );
    if( !code ) break;					/* no more options */
    switch( code )
      {
      case '0': case '1': case '2': case '3': case '4':
      case '5': case '6': case '7': case '8': case '9':
                zero = ( code == '0' );
                encoder_options = option_mapping[code-'0']; break;
      case 'a': ignore_trailing = false; break;
      case 'b': member_size = getnum( arg, 100000, max_member_size ); break;
      case 'c': to_stdout = true; break;
      case 'd': set_mode( &program_mode, m_decompress ); break;
      case 'f': force = true; break;
      case 'F': recompress = true; break;
      case 'h': show_help(); return 0;
      case 'k': keep_input_files = true; break;
      case 'l': set_mode( &program_mode, m_list ); break;
      case 'm': encoder_options.match_len_limit =
                  getnum( arg, min_match_len_limit, max_match_len );
                zero = false; break;
      case 'n': break;
      case 'o': if( strcmp( arg, "-" ) == 0 ) to_stdout = true;
                else { default_output_filename = arg; } break;
      case 'q': verbosity = -1; break;
      case 's': encoder_options.dictionary_size = get_dict_size( arg );
                zero = false; break;
      case 'S': volume_size = getnum( arg, 100000, max_volume_size ); break;
      case 't': set_mode( &program_mode, m_test ); break;
      case 'v': if( verbosity < 4 ) ++verbosity; break;
      case 'V': show_version(); return 0;
      case opt_lt: loose_trailing = true; break;
      default : internal_error( "uncaught option." );
      }
    } /* end process options */

#if defined(__MSVCRT__) || defined(__OS2__) || defined(__DJGPP__)
  setmode( STDIN_FILENO, O_BINARY );
  setmode( STDOUT_FILENO, O_BINARY );
#endif

  num_filenames = max( 1, ap_arguments( &parser ) - argind );
  filenames = resize_buffer( filenames, num_filenames * sizeof filenames[0] );
  filenames[0] = "-";

  for( i = 0; argind + i < ap_arguments( &parser ); ++i )
    {
    filenames[i] = ap_argument( &parser, argind + i );
    if( strcmp( filenames[i], "-" ) != 0 ) filenames_given = true;
    }

  if( program_mode == m_list )
    return list_files( filenames, num_filenames, ignore_trailing, loose_trailing );

  if( program_mode == m_compress )
    {
    if( volume_size > 0 && !to_stdout && default_output_filename[0] &&
        num_filenames > 1 )
      { show_error( "Only can compress one file when using '-o' and '-S'.",
                    0, true ); return 1; }
    Dis_slots_init();
    Prob_prices_init();
    }
  else volume_size = 0;
  if( program_mode == m_test ) to_stdout = false;	/* apply overrides */
  if( program_mode == m_test || to_stdout ) default_output_filename = "";

  output_filename = resize_buffer( output_filename, 1 );
  output_filename[0] = 0;
  if( to_stdout && program_mode != m_test )	/* check tty only once */
    { outfd = STDOUT_FILENO; if( !check_tty_out( program_mode ) ) return 1; }
  else outfd = -1;

  const bool to_file = !to_stdout && program_mode != m_test &&
                       default_output_filename[0];
  if( !to_stdout && program_mode != m_test && ( filenames_given || to_file ) )
    set_signals( signal_handler );

  Pp_init( &pp, filenames, num_filenames );

  const bool one_to_one = !to_stdout && program_mode != m_test && !to_file;
  for( i = 0; i < num_filenames; ++i )
    {
    unsigned long long cfile_size;
    const char * input_filename = "";
    int infd;
    int tmp;
    struct stat in_stats;
    const struct stat * in_statsp;

    Pp_set_name( &pp, filenames[i] );
    if( strcmp( filenames[i], "-" ) == 0 )
      {
      if( stdin_used ) continue; else stdin_used = true;
      infd = STDIN_FILENO;
      if( !check_tty_in( pp.name, infd, program_mode, &retval ) ) continue;
      if( one_to_one ) { outfd = STDOUT_FILENO; output_filename[0] = 0; }
      }
    else
      {
      const int eindex = extension_index( input_filename = filenames[i] );
      infd = open_instream2( input_filename, &in_stats, program_mode,
                             eindex, one_to_one, recompress );
      if( infd < 0 ) { set_retval( &retval, 1 ); continue; }
      if( !check_tty_in( pp.name, infd, program_mode, &retval ) ) continue;
      if( one_to_one )			/* open outfd after verifying infd */
        {
        if( program_mode == m_compress )
          set_c_outname( input_filename, true, true, volume_size > 0 );
        else set_d_outname( input_filename, eindex );
        if( !open_outstream( force, true ) )
          { close( infd ); set_retval( &retval, 1 ); continue; }
        }
      }

    if( one_to_one && !check_tty_out( program_mode ) )
      { set_retval( &retval, 1 ); return retval; }	/* don't delete a tty */

    if( to_file && outfd < 0 )		/* open outfd after verifying infd */
      {
      if( program_mode == m_compress ) set_c_outname( default_output_filename,
                                       filenames_given, false, volume_size > 0 );
      else
        { output_filename = resize_buffer( output_filename,
                            strlen( default_output_filename ) + 1 );
          strcpy( output_filename, default_output_filename ); }
      if( !open_outstream( force, false ) || !check_tty_out( program_mode ) )
        return 1;	/* check tty only once and don't try to delete a tty */
      }

    in_statsp = ( input_filename[0] && one_to_one ) ? &in_stats : 0;
    cfile_size = ( input_filename[0] && S_ISREG( in_stats.st_mode ) ) ?
      ( in_stats.st_size + 99 ) / 100 : 0;
    if( program_mode == m_compress )
      tmp = compress( cfile_size, member_size, volume_size, infd,
                      &encoder_options, &pp, in_statsp, zero );
    else
      tmp = decompress( cfile_size, infd, &pp, ignore_trailing,
                        loose_trailing, program_mode == m_test );
    if( close( infd ) != 0 )
      { show_file_error( pp.name, "Error closing input file", errno );
        set_retval( &tmp, 1 ); }
    set_retval( &retval, tmp );
    if( tmp )
      { if( program_mode != m_test ) cleanup_and_fail( retval );
        else ++failed_tests; }

    if( delete_output_on_interrupt && one_to_one )
      close_and_set_permissions( in_statsp );
    if( input_filename[0] && !keep_input_files && one_to_one &&
        ( program_mode != m_compress || volume_size == 0 ) )
      remove( input_filename );
    }
  if( delete_output_on_interrupt ) close_and_set_permissions( 0 );	/* -o */
  else if( outfd >= 0 && close( outfd ) != 0 )				/* -c */
    {
    show_error( "Error closing stdout", errno, false );
    set_retval( &retval, 1 );
    }
  if( failed_tests > 0 && verbosity >= 1 && num_filenames > 1 )
    fprintf( stderr, "%s: warning: %d %s failed the test.\n",
             program_name, failed_tests,
             ( failed_tests == 1 ) ? "file" : "files" );
  free( output_filename );
  free( filenames );
  ap_free( &parser );
  return retval;
  }
