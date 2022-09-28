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

#define _FILE_OFFSET_BITS 64

#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "lzip.h"
#include "lzip_index.h"


static int seek_read( const int fd, uint8_t * const buf, const int size,
                      const long long pos )
  {
  if( lseek( fd, pos, SEEK_SET ) == pos )
    return readblock( fd, buf, size );
  return 0;
  }


static bool add_error( struct Lzip_index * const li, const char * const msg )
  {
  const int len = strlen( msg );
  void * tmp = resize_buffer( li->error, li->error_size + len + 1 );
  if( !tmp ) return false;
  li->error = (char *)tmp;
  strncpy( li->error + li->error_size, msg, len + 1 );
  li->error_size += len;
  return true;
  }


static bool push_back_member( struct Lzip_index * const li,
                              const long long dp, const long long ds,
                              const long long mp, const long long ms,
                              const unsigned dict_size )
  {
  struct Member * p;
  void * tmp = resize_buffer( li->member_vector,
               ( li->members + 1 ) * sizeof li->member_vector[0] );
  if( !tmp ) { add_error( li, mem_msg ); li->retval = 1; return false; }
  li->member_vector = (struct Member *)tmp;
  p = &(li->member_vector[li->members]);
  init_member( p, dp, ds, mp, ms, dict_size );
  ++li->members;
  return true;
  }


static void Li_free_member_vector( struct Lzip_index * const li )
  {
  if( li->member_vector )
    { free( li->member_vector ); li->member_vector = 0; }
  li->members = 0;
  }


static void Li_reverse_member_vector( struct Lzip_index * const li )
  {
  struct Member tmp;
  long i;
  for( i = 0; i < li->members / 2; ++i )
    {
    tmp = li->member_vector[i];
    li->member_vector[i] = li->member_vector[li->members-i-1];
    li->member_vector[li->members-i-1] = tmp;
    }
  }


static bool Li_check_header_error( struct Lzip_index * const li,
                                   const Lzip_header header )
  {
  if( !Lh_verify_magic( header ) )
    { add_error( li, bad_magic_msg ); li->retval = 2; return true; }
  if( !Lh_verify_version( header ) )
    { add_error( li, bad_version( Lh_version( header ) ) ); li->retval = 2;
      return true; }
  if( !isvalid_ds( Lh_get_dictionary_size( header ) ) )
    { add_error( li, bad_dict_msg ); li->retval = 2; return true; }
  return false;
  }

static void Li_set_errno_error( struct Lzip_index * const li,
                                const char * const msg )
  {
  add_error( li, msg ); add_error( li, strerror( errno ) );
  li->retval = 1;
  }

static void Li_set_num_error( struct Lzip_index * const li,
                              const char * const msg, unsigned long long num )
  {
  char buf[80];
  snprintf( buf, sizeof buf, "%s%llu", msg, num );
  add_error( li, buf );
  li->retval = 2;
  }


static bool Li_read_header( struct Lzip_index * const li, const int fd,
                            Lzip_header header, const long long pos )
  {
  if( seek_read( fd, header, Lh_size, pos ) != Lh_size )
    { Li_set_errno_error( li, "Error reading member header: " ); return false; }
  return true;
  }


/* If successful, push last member and set pos to member header. */
static bool Li_skip_trailing_data( struct Lzip_index * const li, const int fd,
                                   unsigned long long * const pos,
                                   const bool ignore_trailing,
                                   const bool loose_trailing )
  {
  enum { block_size = 16384,
         buffer_size = block_size + Lt_size - 1 + Lh_size };
  uint8_t buffer[buffer_size];
  int bsize = *pos % block_size;		/* total bytes in buffer */
  int search_size, rd_size;
  unsigned long long ipos;
  int i;
  if( *pos < min_member_size ) return false;
  if( bsize <= buffer_size - block_size ) bsize += block_size;
  search_size = bsize;				/* bytes to search for trailer */
  rd_size = bsize;				/* bytes to read from file */
  ipos = *pos - rd_size;			/* aligned to block_size */

  while( true )
    {
    const uint8_t max_msb = ( ipos + search_size ) >> 56;
    if( seek_read( fd, buffer, rd_size, ipos ) != rd_size )
      { Li_set_errno_error( li, "Error seeking member trailer: " );
        return false; }
    for( i = search_size; i >= Lt_size; --i )
      if( buffer[i-1] <= max_msb )	/* most significant byte of member_size */
        {
        Lzip_header header;
        const Lzip_header * header2;
        const Lzip_trailer * const trailer =
          (const Lzip_trailer *)( buffer + i - Lt_size );
        const unsigned long long member_size = Lt_get_member_size( *trailer );
        unsigned dictionary_size;
        bool full_h2;
        if( member_size == 0 )			/* skip trailing zeros */
          { while( i > Lt_size && buffer[i-9] == 0 ) --i; continue; }
        if( member_size > ipos + i || !Lt_verify_consistency( *trailer ) )
          continue;
        if( !Li_read_header( li, fd, header, ipos + i - member_size ) )
          return false;
        if( !Lh_verify( header ) ) continue;
        header2 = (const Lzip_header *)( buffer + i );
        full_h2 = bsize - i >= Lh_size;
        if( Lh_verify_prefix( *header2, bsize - i ) )	/* last member */
          {
          if( !full_h2 ) add_error( li, "Last member in input file is truncated." );
          else if( !Li_check_header_error( li, *header2 ) )
            add_error( li, "Last member in input file is truncated or corrupt." );
          li->retval = 2; return false;
          }
        if( !loose_trailing && full_h2 && Lh_verify_corrupt( *header2 ) )
          { add_error( li, corrupt_mm_msg ); li->retval = 2; return false; }
        if( !ignore_trailing )
          { add_error( li, trailing_msg ); li->retval = 2; return false; }
        *pos = ipos + i - member_size;
        dictionary_size = Lh_get_dictionary_size( header );
        if( li->dictionary_size < dictionary_size )
          li->dictionary_size = dictionary_size;
        return push_back_member( li, 0, Lt_get_data_size( *trailer ), *pos,
                                 member_size, dictionary_size );
        }
    if( ipos == 0 )
      { Li_set_num_error( li, "Bad trailer at pos ", *pos - Lt_size );
        return false; }
    bsize = buffer_size;
    search_size = bsize - Lh_size;
    rd_size = block_size;
    ipos -= rd_size;
    memcpy( buffer + rd_size, buffer, buffer_size - rd_size );
    }
  }


bool Li_init( struct Lzip_index * const li, const int infd,
              const bool ignore_trailing, const bool loose_trailing )
  {
  Lzip_header header;
  unsigned long long pos;
  long i;
  li->member_vector = 0;
  li->error = 0;
  li->insize = lseek( infd, 0, SEEK_END );
  li->members = 0;
  li->error_size = 0;
  li->retval = 0;
  li->dictionary_size = 0;
  if( li->insize < 0 )
    { Li_set_errno_error( li, "Input file is not seekable: " ); return false; }
  if( li->insize < min_member_size )
    { add_error( li, "Input file is too short." ); li->retval = 2;
      return false; }
  if( li->insize > INT64_MAX )
    { add_error( li, "Input file is too long (2^63 bytes or more)." );
      li->retval = 2; return false; }

  if( !Li_read_header( li, infd, header, 0 ) ) return false;
  if( Li_check_header_error( li, header ) ) return false;

  pos = li->insize;		/* always points to a header or to EOF */
  while( pos >= min_member_size )
    {
    Lzip_trailer trailer;
    unsigned long long member_size;
    unsigned dictionary_size;
    if( seek_read( infd, trailer, Lt_size, pos - Lt_size ) != Lt_size )
      { Li_set_errno_error( li, "Error reading member trailer: " ); break; }
    member_size = Lt_get_member_size( trailer );
    if( member_size > pos || !Lt_verify_consistency( trailer ) )
      {							/* bad trailer */
      if( li->members <= 0 )
        { if( Li_skip_trailing_data( li, infd, &pos, ignore_trailing,
              loose_trailing ) ) continue; else return false; }
      Li_set_num_error( li, "Bad trailer at pos ", pos - Lt_size );
      break;
      }
    if( !Li_read_header( li, infd, header, pos - member_size ) ) break;
    if( !Lh_verify( header ) )				/* bad header */
      {
      if( li->members <= 0 )
        { if( Li_skip_trailing_data( li, infd, &pos, ignore_trailing,
              loose_trailing ) ) continue; else return false; }
      Li_set_num_error( li, "Bad header at pos ", pos - member_size );
      break;
      }
    pos -= member_size;
    dictionary_size = Lh_get_dictionary_size( header );
    if( li->dictionary_size < dictionary_size )
      li->dictionary_size = dictionary_size;
    if( !push_back_member( li, 0, Lt_get_data_size( trailer ), pos,
                           member_size, dictionary_size ) )
      return false;
    }
  if( pos != 0 || li->members <= 0 )
    {
    Li_free_member_vector( li );
    if( li->retval == 0 )
      { add_error( li, "Can't create file index." ); li->retval = 2; }
    return false;
    }
  Li_reverse_member_vector( li );
  for( i = 0; ; ++i )
    {
    const long long end = block_end( li->member_vector[i].dblock );
    if( end < 0 || end > INT64_MAX )
      {
      Li_free_member_vector( li );
      add_error( li, "Data in input file is too long (2^63 bytes or more)." );
      li->retval = 2; return false;
      }
    if( i + 1 >= li->members ) break;
    li->member_vector[i+1].dblock.pos = end;
    }
  return true;
  }


void Li_free( struct Lzip_index * const li )
  {
  Li_free_member_vector( li );
  if( li->error ) { free( li->error ); li->error = 0; }
  li->error_size = 0;
  }
