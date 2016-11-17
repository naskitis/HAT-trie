/*******************************************************************************
 * // Begin statement                                                          *
 *                                                                             *
 * Author:        Dr. Nikolas Askitis                                          *
 * Email:         askitisn@gmail.com                                           *
 * Github.com:    https://github.com/naskitis                                  *
 *                                                                             *
 * Copyright @ 2016.  All rights reserved.                                     *
 *                                                                             *
 * Permission to use my software is granted provided that this statement       *
 * is retained.                                                                *
 *                                                                             *
 * My software is for non-commercial use only.                                 *
 *                                                                             *
 * If you want to share my software with others, please do so by               *
 * sharing a link to my repository on github.com.                              *
 *                                                                             *
 * If you would like to use any part of my software in a commercial or public  *
 * environment/product/service, please contact me first so that I may          *
 * give you written permission.                                                *
 *                                                                             *
 * This program is distributed without any warranty; without even the          *
 * implied warranty of merchantability or fitness for a particular purpose.    *
 *                                                                             *
 * // End statement                                                            *
 ******************************************************************************/
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <inttypes.h>
#include <assert.h>

#define MEMORY_EXHAUSTED   "Out of memory mate!"
#define BAD_INPUT          "Can not open or read file provided -___-"

/* convert bytes to megabytes; 1 megabyte = 1000000 bytes. */
#define TO_MB 1000000

/* boolean definitions. */
#define false 0
#define true 1

/* set the minimum character recognized by a trie node, represented by the ASCII-7 table index. The default minimum of
 * 32 maps to whitespace.  Likewise, set the maximum character recognized by a trie node.  The default maximum is the
 * index value of 126, which is the '~' character.  Note, the ASCII-7 characters in the range of 32 to 126 inclusive
 * are printable characters.
 */
#define MIN_RANGE (char)32
#define MAX_RANGE (char)126

/* set the trie node size in bytes.  A trie directly maps to all characters of the ASCII-7 table, so 128 pointers
 * are required (of which, only those between MIN_RANGE and MAX_RANGE inclusive are used). Since we are dealing with a
 * 64-bit architecture, each pointer will be 8-bytes long.  The size of each trie node is thus, 8x128 bytes.
 */
#define TRIE_SIZE 1024

/* the following symbolic constant represents an estimate of the number of bytes chewed up each memory allocation
 * request, that is, each malloc or calloc system call.  On a 64-bit Linux operating system, this is typically 16 bytes.
 */
#define ALLOC_OVERHEAD 16

/* the offset from the start of a container, in bytes, where the field used to store the number of keys in a
 * bucket starts.
 */
#define KEYS_IN_BUCKET 0

/* the total number of bytes used for housekeeping in each container. The default (and recommended) is 4 bytes.
 * The first byte is unused, kept for alignment, the second byte is used to represent the end-of-string flag (see
 * paper), and the remaining two are cast into a short, which is used to represent the number of keys in the
 * container. That's why KEYS_IN_BUCKET, shown previously, has an offset of 2.  The first byte is at offset 0,
 * second byte at offset 1, and the third byte at offset 2.
 */
#define BUCKET_OVERHEAD 8

/* we use the 31st pointer of each trie node to store the end-of-string flag (see paper) it must always map to a
 * pointer smaller than MIN_RANGE.
 */
#define STR_CONSUME_FLAG_TRIE 31

/* the number of bytes you must offset from each container to acquire the end-of-string flag, which is stored in
 * one byte.
 */
#define STR_CONSUME_FLAG_BUCKET 4

/* symbolic constants used to represent 32-bit and 64-bit: legacy from the array hash programming back in late 2004. */
#define _32_BYTES 32
#define _64_BYTES 64

typedef struct timeval timer;

double perform_insertion(char *to_insert);
double perform_search(char *to_search);
void fatal(char *str); 
uint32_t get_inserted();
uint32_t get_found();
void set_terminator(char *buffer, int length);
void node_cpy(uint32_t *dest, uint32_t *src, uint32_t bytes);

static int total_searched=0;
static int total_inserted=0;
static int _inserted=0;
static int _found=0;

/* the following is used to maintain trie nodes in a cache-and-space efficient manner. trie nodes are allocated
 * from pre-allocated slab of memory, known as a trie pack. We begin by allocating a single trie pack that can store up
 * to 1024 (1024 byte) trie nodes. This is represented by 'trie_pack_entry_capacity' which is anchored from the first
 * pointer in the 'trie_pack_array', which is an array of pointers. The total number of pointers in this array is
 * represented by 'trie_pack_array_capacity'. This is fixed for now, but it can be made dynamic; the total number of
 * trie nodes supported by default is 262,144. A simple call to realloc can be made to increase the number of pointers
 * in 'trie_pack_array' by increasing 'trie_pack_array_idx' to a larger number. However, this should not be required by
 * the HAT-trie, since the number of trie nodes allocated should be low (see paper).  Finally, trie_counter is used to
 * point to the next available trie node in the current trie_pack. This setup helps improve performance by allocating
 * trie node in contiguous chunks of memory, and also helps reduce memory allocation overheads.  It also provides an
 * efficient manner of determining whether a pointer point to a trie node or a bucket, which is important to
 * performance.
 */
static char **trie_pack_array=NULL;
static uint32_t trie_pack_array_idx=0;
static uint32_t trie_pack_array_capacity=2048;
static uint32_t trie_pack_entry_capacity=1512;
static uint32_t trie_counter=0;
static uint32_t total_trie_pack_memory=0;

/* set the default number of slots in each container (see paper). */
static uint64_t HASH_SLOTS=512;

/* the default bucket size, this will be set later */
static uint64_t BUCKET_SIZE=0;

/* the bucket threshold (number of strings) to trigger a burst (see paper) */
static uint64_t BUCKET_SIZE_LIM=65536;

/* this is where the magic starts, the pointer to the root_trie node :D */
static char *root_trie=0;

/* some state counting variables. */
static uint64_t inserted=0;
static uint64_t searched=0;
static uint64_t num_buckets=0;
static uint64_t num_tries=0;
static uint64_t bucket_mem=0;
static uint64_t max_trie_depth=0;
static uint64_t depth_accumulator=0;

/* function prototype used to free all memory. */
static void HAT_trie_destroy();
static void HAT_trie_burst(char *bucket, char path, char **c_trie);

int snprintf(char *str, size_t size, const char *format, ...);

/* function prototype to split pure bucket/container (this is a pure HAT-trie, so all buckets are termed as 'pure',
 * meaning, all the strings in a bucket/container share the same prefix).
 */
static void split_pure(char *bucket, char **c_trie);

/* function prototype for the array hash table, used to resize dynamic arrays in a cache-efficient manner. */
static void make_aligned_space(char **hash_table, uint32_t idx, uint32_t array_offset,
                               uint32_t required_increase);

/* bitwise hash function for null-terminated strings. */
static uint32_t bitwise_hash(char *word)
{
  char c; unsigned int h=220373;
  for ( ; ( c=*word ) != '\0'; word++ ) h ^= ((h << 5) + c + (h >> 2));
  return ((unsigned int)((h&0x7fffffff) & (HASH_SLOTS-1) ));
}

/* bitwise hash function for length-bounded strings. */
static uint32_t bitwise_hash_len(char *word, uint32_t len)
{
  char c; unsigned int h=220373;
  for ( ; ( c=*word ) && len != 0; word++, len--) h ^= ((h << 5) + c + (h >> 2));
  return ((unsigned int)((h&0x7fffffff) & (HASH_SLOTS-1) ));
}

/*
 * resizes (or creates) a dynamic array that is anchored to a hash slot. This version supports exact-fit and paging array growth.
 */
void resize_array(char **hash_table, uint32_t idx, uint32_t array_offset, uint32_t required_increase)
{
  /* if there is no slot, then create one with respect to the growth policy used */
  if(array_offset == 0)
  {
    #ifdef EXACT_FIT
   
    if ((*(hash_table + idx) = malloc(required_increase)) == NULL) fatal(MEMORY_EXHAUSTED);
    
    /* keep track of the amount of memory allocated */
    //hash_mem += required_increase + 16;  
   
    #else    

    /* otherwise, grow the array with paging */
    /* if the required space is less than 32 bytes, than allocate a 32 byte block */
    if(required_increase <= _32_BYTES)
    {
      if ((*(hash_table + idx) = (char *) malloc(_32_BYTES)) == NULL) fatal(MEMORY_EXHAUSTED);  
      //hash_mem += _32_BYTES + 16;  
    }
    /* otherwise, allocate as many 64-byte blocks as required */
    else
    {
      uint32_t number_of_blocks = ((int)( (required_increase-1) >> 6)+1);   

      if ((*(hash_table + idx) = (char *) malloc(number_of_blocks << 6)) == NULL) fatal(MEMORY_EXHAUSTED);
         
      /* keep track of the amount of memory allocated */ 
      //hash_mem += (number_of_blocks << 6) + 16; 
    }
    
    #endif
  }
  else
  {
    /* otherwise, a slot entry (an array) is found which must be resized */
    #ifdef EXACT_FIT

    char *tmp = malloc(array_offset+required_increase);
    if(tmp == NULL) fatal (MEMORY_EXHAUSTED);
    
    /* copy the existing array into the new one */
    memcpy(tmp, *(hash_table + idx), array_offset+1);
    
    /* free the old array and assign the slot pointer to the new array */ 
    free( *(hash_table + idx) );
    *(hash_table + idx) = tmp;
 
    /* keep track of the amount of memory allocated */
    //hash_mem = hash_mem - 1 + required_increase; 
    
    /* else grow the array in blocks or pages */
    #else 
    
    uint32_t old_array_size = array_offset + 1;
    uint32_t new_array_size = (array_offset+required_increase);
    
    /* if the new array size can fit within the previously allocated 32-byte block, 
     * then no memory needs to be allocated.
     */
    if ( old_array_size <= _32_BYTES  &&  new_array_size <= _32_BYTES )
    {
      return;
    }
    /* if the new array size can fit within a 64-byte block, then allocate only a
     * single 64-byte block.
     */
    else if ( old_array_size <= _32_BYTES  &&  new_array_size <= _64_BYTES)
    {  
      char *tmp = malloc(_64_BYTES);
      if(tmp == NULL) fatal (MEMORY_EXHAUSTED);
      
      /* copy the old array into the new */
      memcpy( tmp,  *(hash_table + idx), old_array_size);
      
      /* delete the old array */ 
      free( *(hash_table + idx) );

      /* assign the slot pointer to the new array */
      *(hash_table + idx) = tmp;

      /* accumulate the amount of memory allocate */
      //hash_mem += _32_BYTES;
   
      return;
    }
    /* if the new array size can fit within a 64-byte block, then return */
    else if  (old_array_size <= _64_BYTES && new_array_size <= _64_BYTES )
    {
      return;
    }
    /* resize the current array by as many 64-byte blocks as required */
    else
    {
      uint32_t number_of_blocks = ((int)( (old_array_size-1) >> 6) + 1);
      uint32_t number_of_new_blocks = ((int)( (new_array_size-1) >> 6) + 1);

      if(number_of_new_blocks > number_of_blocks)
      {
        /* allocate as many blocks as required */
        char *tmp = malloc(number_of_new_blocks << 6);
        if (tmp==NULL) fatal(MEMORY_EXHAUSTED);
        
        /* copy the old array, a word at a time, into a new array */
        node_cpy( (uint32_t *) tmp, (uint32_t *) *(hash_table + idx), number_of_blocks<<6); 
        
        /* free the old array */
        free( *(hash_table + idx) );
        
        /* assign the slot pointer to the new array */
        *(hash_table + idx) = tmp;

        /* keep track of the number of bytes allocated */
        //hash_mem += ((number_of_new_blocks-number_of_blocks)<<6); 
      } 
    } 

  #endif 
  }
}


/* look for a string in the array hash table. */
static uint32_t hash_lookup(char **hash_table, char *query_start)
{
   char *array, *query=query_start, *word_start;
   uint32_t register len=0;

   /* access the required slot and fetch its array, if any. */
   if( (array = *(hash_table + bitwise_hash(query_start)) ) == NULL)  return false;

   /* enter a loop to search for the required string. */
   loop:
   query=query_start;

   /* calculate the length of the current string in the array.  Up to the first two bytes can be used to store the
    * length of the string (see paper).
    */
   if( (len = (unsigned int) *array ) >= 128)
     len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) );

   /* move to the first character of the current string. */
   ++array;

   /* remember the start of the string. */
   word_start = array;

   /* go ahead and scan the current string in the array, comparing it to the query string, character by character until
    * mismatch or eof. Note:  you can speed up the comparison here if strings are 0xff terminated. e.g: aeroplace0xff 
    * This is faster because you dont have to check for '\0' or *query != '\0'. Under skew search, you can boost performance
    * by a couple of seconds. But the problem is, this could lead to unfair comparisions, since most other data structures 
    * out there are designed to handle null-terminated strings.  So best stick with processing strings that are null 
    * terminated. 
    */
   for (; *query != '\0' && *query == *array; ++query, ++array);

   /* you know its a match if all the characters in the query string have been matched and the length of the strings
    * match.
    */
   if ( *query == '\0' && (array-word_start) == len ) return true;

   /* on mismatch, skip the current string and fetch the next. */
   array = word_start + len;

   /* if you've reached the and of the array, then the search is over. */
   if (*array == '\0') return false;

   goto loop;
}

/* insert a string into the array hash table. */
static uint32_t hash_insert(char **hash_table, char *query_start)
{
   char *array, *array_start, *query=query_start, *word_start;
   uint32_t array_offset;
   uint32_t register len, idx;

   /* get the required slot. */
   idx=bitwise_hash(query_start);

   /* get the required slot. */
   if( (array = *(hash_table + idx)) == NULL)
   {
     array_start=array;
     goto insert;
   }

   /* remember the start of the array. */
   array_start=array;

   /* enter a loop to search for the required string. */
   loop:
   query=query_start;

   /* calculate the length of the current string in the array.  Up to the first two bytes can be used to store the
    * length of the string (see paper).
    */
   if( ( len = (unsigned int) *array ) >= 128 )
     len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) );

   /* move to the first character of the current string. */
   ++array;

   /* remember the start of the string. */
   word_start = array;

   /* go ahead and scan the current string in the array, comparing it to the query string, character by character until
    * mismatch or eof. Note:  you can speed up the comparison here if strings are 0xff terminated. e.g: aeroplace0xff 
    * This is faster because you dont have to check for '\0' or *query != '\0'. Under skew search, you can boost performance
    * by a couple of seconds. But the problem is, this could lead to unfair comparisions, since most other data structures 
    * out there are designed to handle null-terminated strings.  So best stick with processing strings that are null 
    * terminated.  
    */
   for (; *query != '\0' && *query == *array; ++query, ++array);

   /* you know its a match if all the characters in the query string have been matched and the length of the strings
    * match.
    */
   if ( *query == '\0' && (array-word_start) == len ) return false;

   /* on mismatch, skip the current string and fetch the next. */
   array = word_start + len;

   /* if you've reached the and of the array, then the search is over. */
   if (*array == '\0')  goto insert;

   goto loop;

   /* we have determined that the string does not exist, so lets add it. */
   insert:

   /* get the length of the query. */
   for(; *query != '\0'; query++);
   len = query - query_start;

   /* get the size of the current array in bytes. */
   array_offset = array-array_start;

   /* resize the array. */
   resize_array(hash_table, idx, array_offset, ( len < 128 ) ? len+2 : len+3);

   /* make sure you re-assign the array to the correct hash slot, since its physical address in memory may
    * have changed.
    */
   array = *(hash_table+idx);

   /* move to the end of the array. */
   array_start = array;
   array += array_offset;

   /* store the length of the string in one or two bytes as needed. */
   if( len < 128 )
   {
     *array = (char) len;
   }
   else
   {
     *array     = (char) ( len >> 8) | 0x80;
     *(++array) = (char)  len; 
   }
   ++array;

   /* copy/append the string to the bucket. */
   while( *query_start != '\0')
   {
     *array++ = *query_start++;
   }

   /* make sure you null terminate the bucket, to serve as a end-of-bucket flag. */
   *array='\0';
   return true;
}

/* similar to the function as above, except that now we provide the string length as a parameter and we don't bother
 * searching for the string.  We simply scan the end of the array, resize it, then append the string.  This function
 * will typically be used when we burst a container in the HAT-trie.
 */
static uint32_t hash_insert_with_len(char **hash_table, char *query_start, uint32_t len)
{
   char *array, *array_start;
   uint32_t array_offset, idx, skip_len=0;

   /* hash the string using the bitwise hash function. */
   idx=bitwise_hash_len(query_start, len);

   /* access the required hash slot and its array. */
   if( (array = *(hash_table + idx)) == NULL)
   {
     array_start=array;
     goto insert;
   }
   array_start=array;

   /* skip along the array until you reach the end, so you can determine its size. */
   while(*array != '\0')
   {
     if( ( skip_len = (unsigned int) *array ) >= 128 )
       skip_len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array)  );

     array = (array+1) + skip_len;
   }

   insert:

   /* calculate the size of  the array in bytes. */
   array_offset = array-array_start;

   /* resize the array and re-assign it to its hash slot, just in case it has been moved to a new physical location
    * in memory.
    */
   resize_array(hash_table, idx, array_offset, ( len < 128 ) ? len+2 : len+3);
   array = *(hash_table+idx);
   array_start = array;

   /* move to the end of the array. */
   array += array_offset;

   /* calculate the length of the string, which we store in either one or two bytes */
   if( len < 128 )
   {
     *array = (char) len;
   }
   else
   {
     *array     = (char) ( len >> 8) | 0x80;
     *(++array) = (char) len;
   }
   ++array;

   /* copy/append the string to the array. */
   while( len!=0 )
   {
     *array++ = *query_start++; --len;
   }

   /* make sure you terminate the bucket with a null, to serve as the end-of-bucket flag. */
   *array='\0';
   return true;
}

/* allocate a new trie node, using the trie_pack structure discussed above. */
static char * new_trie()
{
  /* if the current trie_pack is full, allocate a new one */
  if(trie_counter == trie_pack_entry_capacity)
  {
    trie_pack_array_idx++;

    /* make sure we don't allocate more trie_packs than we have pointers for. */
    assert(trie_pack_array_idx < trie_pack_array_capacity);

    /* allocate a new trie pack and resize the trie_counter */
    *(trie_pack_array+trie_pack_array_idx) = calloc(trie_pack_entry_capacity*TRIE_SIZE, sizeof(char));
    trie_counter=0;
  }

  /* return a pointer to the next available space in the trie_pack. */
  return *(trie_pack_array + trie_pack_array_idx) + (trie_counter++ * TRIE_SIZE);
}

/* determine whether a pointer points to a trie node or a bucket without dereferencing it. This is a handy function
 * which can improve the efficiency of trie-based data structures.
 */
static int is_it_a_trie(char *x)
{
  register uint64_t idx=0;
  for(; idx <= trie_pack_array_idx; idx++)
     if ( x >= *(trie_pack_array+idx) && x <= (*(trie_pack_array+idx)+(TRIE_SIZE * (trie_pack_entry_capacity-1))))
       return true;

  return false;
}

/* create a new bucket/container for the HAT-trie, which is simply an array of slots+the overhead. */
static char * new_bucket()
{
  char *tmp=calloc(BUCKET_SIZE, sizeof(char));
  assert(tmp != NULL);
  return tmp;
}

/* determine whether a bucket/container has reached its capacity. */
static uint64_t full(char *bucket)
{
  uint32_t *consumed;
  if(bucket == NULL) return false;

  consumed = (uint32_t *)(bucket+KEYS_IN_BUCKET);

  /* a container is deemed to be full once it contains more than BUCKET_SIZE_LIM strings. */
  if(*consumed > BUCKET_SIZE_LIM )
    return true;
  else
    return false;
}

/* we need to initialize the HAT-trie before we use it. */
static void HAT_trie_init()
{
  /* allocate the array of pointers used to maintain the trie packs and initialize its counters. */
  trie_pack_array = (char **) calloc (trie_pack_array_capacity, sizeof(char *));
  trie_pack_array_idx=0;
  trie_counter=0;

  /* allocate the first trie pack and assign it  to the first pointer of the trie_pack_array. */
  *(trie_pack_array+trie_pack_array_idx) = calloc(trie_pack_entry_capacity*TRIE_SIZE, sizeof(char));
  assert(*(trie_pack_array+trie_pack_array_idx) != NULL);

  /* allocate the root trie node and initialize the trie node pointer. */
  root_trie=new_trie();
  num_tries=1;

  /* calculate an empty bucket/container size. */
  BUCKET_SIZE = (HASH_SLOTS * 8) + BUCKET_OVERHEAD;
}

/* search the HAT-trie for a null-terminated string. */
uint64_t search(char *word)
{
  char **c_trie = (char **)root_trie;
  char *x;

  /* process the query string a character at a time, from left to right, until all characters are exhausted. */
  while( *word != '\0')
  {
    /* fetch the corresponding trie node pointer, if its null, then the string isn't in the HAT-trie. */
    if ( (x = *(c_trie + *word)) == NULL) return 0;

    /* if the pointer is not null, then determine what it points to. */
    if ( is_it_a_trie (x) )
    {
      c_trie= (char **)x;
    }
    /* it points to a bucket/container. */
    else
    {
      /* consume the lead character of the query string. */
      word++;

      /* if the query string has been exhausted, then check if the containers end-of-string flag is set. */
      if( *word == '\0')
      {
        if(*(x+STR_CONSUME_FLAG_BUCKET))
        {
          return true;
        }
        else
        {
          return false;
        }
      }

      /* lookup the containers hash table to determine if the string (suffix) exists. */
      return hash_lookup((char **)(x+BUCKET_OVERHEAD), word);
    }

    word++;
  }

  /* if we have consumed the entire query string and haven't reached a container, then we must check the last trie node
   * we accessed to determine whether or not the string exists.
   */
  if( *(uint32_t *)(c_trie+STR_CONSUME_FLAG_TRIE))
  {
    return true;
  }
  else
  {
    return false;
  }
}

/* create a new bucket/container, initialize its data field, attach it to a parent trie, and insert the remaining query
 * string into its hash table.
 */
static uint64_t new_container(char **c_trie, char path, char *word)
{
  char *x;

  /* allocate space for a new bucket. */
  x=new_bucket();

  /* clear the string exhaust flag. */
  *(x+STR_CONSUME_FLAG_BUCKET)=0;

  /* clear the key counter */
  *(uint32_t *)(x+KEYS_IN_BUCKET)=0;

  /* assign the container to the parent trie node. */
  *(c_trie + path)=x;

  /* if the string has been consumed, then we simply set the buckets end-of-string flag to complete the
   * insertion, otherwise we insert what remains of the string into the containers hash table.
   */
  if( *word == '\0')
  {
    *(x+STR_CONSUME_FLAG_BUCKET) = 1;
  }
  else
  {
    hash_insert((char **)(x+BUCKET_OVERHEAD), word);
    *(uint32_t *)(x+KEYS_IN_BUCKET) += 1;
  }

  /* keep track of the number of buckets allocated. */
  ++num_buckets;
  return true;
}

/* insert a null-terminated string into the HAT_trie. */
uint64_t insert(char *word)
{
  char **c_trie=  (char **) root_trie;
  char *x;

  /* process the query string a character at a time, from left to right, until all characters are exhausted. */
  while( *word != '\0')
  {
    /* fetch the corresponding trie node pointer, if its null, then we create a new container. */
    if ( (x = *(c_trie +  *word)) == NULL)  return new_container(c_trie, *word, word+1);

    /* if the pointer is not null, then determine what it points to. */
    if( is_it_a_trie (x) )
    {
      c_trie=(char  **)x;
    }
    /* it points to a bucket/container. */
    else
    {
      word++;

      /* if the string has been consumed, then we check the buckets end-of-string flag. If it is set, then the string
       * already exists, otherwise we set it to complete the insertion.
       */
      if( *word == '\0' )
      {
        if( *(x+STR_CONSUME_FLAG_BUCKET))
	{
	  return false;
	}
        else
	{
	  *(x+STR_CONSUME_FLAG_BUCKET) = 1;
	  return true;
	}
      }

      /* attempt to insert what remains of the string into the containers hash table. */
      if(hash_insert((char **)(x+BUCKET_OVERHEAD), word))
      {
        *(uint32_t *)(x+KEYS_IN_BUCKET) += 1;

        /* see if we need to burst the container. */
        if(full(x))
          HAT_trie_burst(x, *(word-1), c_trie);

        return true;
      }
      /* the string was found in the containers hash table. */
      return false;
    }

    /* move to the next character in the string to insert. */
    ++word;
  }

  /* if we consumed the string prior to reaching any container, then we must set the end-of-string flag in the last
   * trie node accessed, unless its already set, in which case, the insertion fails.
   */
  if(  *(uint32_t *)(c_trie+STR_CONSUME_FLAG_TRIE))
  {
    return false;
  }
  else
  {
    *(uint32_t *)(c_trie+STR_CONSUME_FLAG_TRIE) = 1;
    return true;
  }
}

/* burst a HAT_trie container. */
static void HAT_trie_burst(char *bucket, char path, char **c_trie)
{
  char *n_trie;

  /* allocate a new trie node to become the new parent. */
  n_trie = new_trie();
  *(c_trie+path)=n_trie;

  c_trie = (char **) n_trie;
  num_tries++;

  /* transfer the containers end-of-string flag into the parent trie node and clear the containers end-of-string flag */
  *(uint64_t *)(c_trie+STR_CONSUME_FLAG_TRIE) = (uint64_t ) *(bucket+STR_CONSUME_FLAG_BUCKET);
  *(bucket+STR_CONSUME_FLAG_BUCKET)=0;

  /* we are splitting a pure bucket/container (see paper). */
  split_pure(bucket, c_trie);
}

/* how we burst a pure HAT-trie container. */
static void split_pure(char *bucket, char **c_trie)
{
  char *array, *slot, *word_start;
  char *x;
  uint32_t len;
  register int i=0;

  /* access each hash slot in a container. */
  for(i=0; i<HASH_SLOTS; ++i)
  {
    array = *(((char **)(bucket+BUCKET_OVERHEAD))+i);
    if(array==NULL) continue;

    /* remember the start of the array. */
    slot=array;

    /* we now process the current hash slot to traverse all of its strings. */
    while(*array != '\0')
    {
      /* get the length of the current string */
      if( (len = (unsigned int) *array ) >= 128)
        len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) );

      /* go to the start of the string and record its position. */
      array++;
      word_start = array;

      /* access the first character of the string and map it to the parent trie node, to acquire the
       * corresponding trie node pointer.
       */
      x = *(c_trie + *array);

      /* create and initialize a new bucket, and assign it to the corresponding trie node pointer, which is located
       * by mapping the first character of the string into the parent trie node. create a new bucket and assign it
       * to the pointer, if the pointer is null.
       */
      if (x == NULL)
      {
        x=new_bucket();
        *(x+STR_CONSUME_FLAG_BUCKET)=0;
        *(uint32_t *)(x+KEYS_IN_BUCKET)=0;
        *(c_trie + *array)=x;
        ++num_buckets;
      }

      /* if the length of the string is now zero (since we strip away the lead character), set the buckets
       * string-exhaust flag.
       */
      if( (len-1)==0 )
      {
        *(x+STR_CONSUME_FLAG_BUCKET)=1;
      }
      /* insert what remains of the string into the containers hash table. Note, since we added a new trie node as a
       * parent, all of the strings in this bucket will be truncated by one character, thus the array+1 and len-1
       * parameters shown below.
       */
      else
      {
        hash_insert_with_len((char **)(x+BUCKET_OVERHEAD), array+1, len-1);
        *(uint32_t *)(x+KEYS_IN_BUCKET)+=1;
      }

      /* skip to the next string in the bucket */
      array = word_start  +  len;
    }

    /* once your done, free the hash slot */
    free(slot);
  }

  /* all of the buckets strings have been processed, its now time to delete the bucket itself. */
  --num_buckets;
  free(bucket);
}

/* this is a recursive function, designed to traverse the HAT_trie in order, so you can delete its nodes. */
void in_order(char **c_trie, int local_depth)
{
  int i=0, j=0;
  char *x;
  char *slot;

  if(local_depth > max_trie_depth)  max_trie_depth=local_depth;

  /* access all used pointers in a trie node */
  for(i=MIN_RANGE; i<MAX_RANGE; ++i)
  {
    if ( (x = *(c_trie + i)) == NULL) continue;

    /* if the pointer points to a trie node, then move down the tree structure by recursively applying this function. */
    if ( is_it_a_trie(x) )
    {
      in_order( (char **)x, local_depth+1);
    }
    /* once you hit a container, then access each of its slots */
    else
    {
      for(j=0; j<HASH_SLOTS; j++)
      {
        slot=*(((char **)(x+BUCKET_OVERHEAD))+j);

        /* if the slot is used, traverse its assigned array to determine its size, then delete it. */
	if ( slot != NULL )
   	{
	  char *slot_start = slot;

          /* you can probably do this more efficiently by skipping, but since your deleting the entire bucket, it easier
           * just to look for the null character.
           */
	  while(*slot != '\0') slot++;

          /* keep tabs on the amount of space allocated, taking into consideration the operating system overhead
           * estimate.
           */
          bucket_mem += (slot-slot_start) + 1 + ALLOC_OVERHEAD;
	  free(slot_start);
        }
      }
      depth_accumulator+=local_depth;
    }
  }
}

/* completely free the memory allocated by the HAT-trie */
static void HAT_trie_destroy()
{
  int i=0;
  in_order((char **)root_trie, 1);

  /* free all the trie packs and calculate the total memory consumed by them */
  for(i=0; i<=trie_pack_array_idx; ++i)
  {
    total_trie_pack_memory += (((trie_pack_entry_capacity*TRIE_SIZE) + sizeof(char))+ALLOC_OVERHEAD);
    free ( *(trie_pack_array + i ) );
  }

  /* free the trie_pack array */
  free(trie_pack_array);
}

double perform_insertion(char *);
double perform_search(char *);

/* where the magic starts */
int main(int argc, char **argv)
{
   double mem=0, insert_real_time=0.0, search_real_time=0.0;
   uint64_t vsize=0, num_files=0, i=0, j=0;
   char *to_insert=NULL, *to_search=NULL;

   
   if(argv[1]==NULL || argv[2] == NULL || argv[3] == NULL)
   {
     puts("Incorrect usage :|");
     puts("./nikolas_askitis_hat_trie [slots] [limit] [num-file-insert] [file1 file2 ...] [num-file-search] [file1 file2 ...]");
     puts("example: ./nikolas_askitis_hat_trie 8192 65536 1 distinct 2 skew_1 skew_2");
     exit(1);
   }
   /* be careful what you choose here, since hash slots and bucket limit impact space consumption */
   /* get the number of hash slots per bucket, must be power of 2*/
   HASH_SLOTS = atoi(argv[1]);

   /* get the specified bucket size */
   BUCKET_SIZE_LIM = atoi(argv[2]);

   /* make sure the user supplied a valid bucket size */
   if (BUCKET_SIZE_LIM < 8192 || BUCKET_SIZE_LIM > 10000000)
   {
     puts("Keep bucket size between 8192 and 10000000 strings");
     exit(1);
   }

   /* get the number of files to insert */
   num_files = atoi(argv[3]);

   /* initialize the HAT-trie */
   HAT_trie_init();

   /* insert each of the files specified, accumulating the time required to insert each file */
   for(i=0, j=4; i<num_files; ++i, ++j)
   {
     to_insert=argv[j];
     insert_real_time+=perform_insertion(to_insert);
   }

   /* get the virtual memory size of the process after inserting all of the files/strings.  This will capture
    * space-overheads from memory allocation and memory fragmentation.
    */
   {
     FILE * statf;
     char fname[1024];
     char commbuf[1024];
     char state;
     pid_t mypid;
     uint64_t ppid, pgrp, session, ttyd, tpgid, flags, minflt, cminflt, majflt, cmajflt;
     uint64_t utime, stime, cutime, cstime, counter, priority, timeout, itrealvalue;
     uint64_t starttime, rss, rlim, startcode, endcode, startstack, kstkesp, ksteip;
     uint64_t signal, blocked, sigignore, sigcatch, wchan, ret, pid;

     mypid = getpid();
     snprintf(fname, 1024, "/proc/%u/stat", mypid);
     statf = fopen(fname, "r");
     ret = fscanf(statf, "%lu %s %c %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu "
                         "%lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu",
                  &pid, commbuf, &state, &ppid, &pgrp, &session, &ttyd, &tpgid, &flags, &minflt, &cminflt, &majflt,
                  &cmajflt, &utime, &stime, &cutime, &cstime, &counter, &priority, &timeout, &itrealvalue,
                  &starttime, &vsize, &rss, &rlim, &startcode, &endcode, &startstack, &kstkesp, &ksteip, &signal,
                  &blocked, &sigignore, &sigcatch, &wchan);

     if (ret != 35)
        fprintf(stderr, "Failed to read all 35 fields, only %lu decoded\n", ret);

     fclose(statf);
   }

   /* get the number of files to search */
   num_files = atoi(argv[j++]);

   /* search each of the files specified and accumulate the search time */
   for(i=0; i<num_files; i++, j++)
   {
     to_search=argv[j];
     search_real_time+=perform_search(to_search);
   }

   /* free up all memory allocated by the HAT-trie */
   HAT_trie_destroy();

   /* Input format:
    * ./nikolas_askitis_hat_trie [slots] [limit] [num-file-insert] [file1 file2 ...] [num-file-search] [file1 file2 ...]
    * 
    * Format of output:
    * HAT-trie 104.43 94.91 3.94 2.61 6000000 6000000 512 16384  ...
    *           (1)    (2)   (3)  (4)   (5)     (6)   (7)  (8)   (9)
    * Legend:
    * 1.  the virtual memory size (MB)
    * 2.  the estimated memory size (MB)
    * 3.  elapsed time to insert (sec)
    * 4.  elapsed time to search (sec)
    * 5.  number of strings successfully inserted
    * 6.  number of strings successfully found
    * 7.  number of slots allocated in each container
    * 8.  bucket threshold
    * 9.  number of tries allocated
    * 10. number of buckets allocated
    * 11. contact and copyright info.
    */

   mem=((total_trie_pack_memory/(double)TO_MB)  /*((num_tries*(TRIE_SIZE+16))/(double)TO_MB)*/ +
        ((num_buckets*(BUCKET_SIZE+ALLOC_OVERHEAD))/(double)TO_MB)+bucket_mem/(double)TO_MB);
   
#ifndef EXACT_FIT
      /* the mem counter is only configured to work with EXACT_FIT.  When paging is used, rely on the process size */
      printf("HAT-trie %.2f %.2f %.2f %.2f %lu %lu %lu %lu %lu %lu (pure HAT-trie) PAGING (use process size) --- Dr. Nikolas Askitis "
          "Copyright @ 2016 askitisn@gmail.com\n",
          vsize / (double) TO_MB, mem, insert_real_time, search_real_time, get_inserted(), get_found(), (uint64_t) HASH_SLOTS,
          BUCKET_SIZE_LIM, num_tries, num_buckets);
   
#else
   printf("HAT-trie %.2f %.2f %.2f %.2f %lu %lu %lu %lu %lu %lu (pure HAT-trie) EXACT_FIT --- Dr. Nikolas Askitis "
          "Copyright @ 2016 askitisn@gmail.com\n",
          vsize / (double) TO_MB, mem, insert_real_time, search_real_time, get_inserted(), get_found(), (uint64_t) HASH_SLOTS,
          BUCKET_SIZE_LIM, num_tries, num_buckets);
#endif
   
#ifndef EXACT_FIT
   
   
#endif
   
  return true;
}



/* display an error message and exit the program */
void fatal(char *str) { puts(str); exit(1); }

/* copy a block of memory, a word at a time */
void node_cpy(uint32_t *dest, uint32_t *src, uint32_t bytes)
{
  bytes=bytes>>2;
  while(bytes != 0)
  {
    *dest++=*src++; 
    bytes--;
  } 
}

/* 
 * scan an array of characters and replace '\n' characters
 * with '\0' 
 */
void set_terminator(char *buffer, int length)
{
  register int32_t i=0;
  for(; i<length; ++i)  
  {
    if( *(buffer+i) == '\n' )   
    {
      *(buffer+i) = '\0';
    }
  }
}

void reset_counters()
{
  total_searched=total_inserted=_inserted=_found=0;
}

uint32_t get_inserted()
{
  return _inserted;
}

uint32_t get_found()
{
  return _found;
}

/* access the data structure to insert the strings found in the 
 * filename that is provided as a parameter. The file supplied must
 * be smaller than 2GB in size, otherwise, the code below has to be
 * modified to support large files, i.e., open64(), lseek64().
 * This should not be required, however, since the caller to this
 * function should be designed to handle multiple files, to allow you 
 * to break a large file into smaller pieces.  
 */
double perform_insertion(char *to_insert)
{ 
   int32_t  input_file=0;
   int32_t  return_value=0;
   uint32_t input_file_size=0;
   uint32_t read_in_so_far=0;

   char *buffer=0;
   char *buffer_start=0;
   
   timer start, stop;
   double insert_real_time=0.0;
   
   /* open the file for reading */
   if( (input_file=(int32_t) open(to_insert, O_RDONLY))<=0) 
     fatal(BAD_INPUT);  
     
   /* get the size of the file in bytes */
   input_file_size=lseek(input_file, 0, SEEK_END);
     
   /* allocate a buffer in memory to store the file */
   if( (buffer = (char *)calloc(1, input_file_size+1 )) == NULL) 
     fatal(MEMORY_EXHAUSTED);
     
   /* keep a pointer to the start of the buffer */
   buffer_start=buffer;
   
   /* read the file into memory and close the file pointer */
   lseek(input_file, 0, SEEK_SET);

   /* attempt to read the entire file into memory */
   while(read_in_so_far < input_file_size)
   {
     return_value=read(input_file, buffer, input_file_size);
     assert(return_value>=0);
     read_in_so_far+=return_value;
   }
   close(input_file);
   
   /* make sure that all strings are null terminated */
   set_terminator(buffer, input_file_size);
   
   /* start the timer for insertion */  
   gettimeofday(&start, NULL);

   /* main insertion loop */
   time_loop_insert: 

   /* insert the first null-terminated string in the buffer */
   if(insert(buffer))
   {
     _inserted++;
   } 
   total_inserted++;

   /* point to the next string in the buffer */
   for(; *buffer != '\0'; buffer++);
   buffer++;

   /* if the buffer pointer has been incremented to beyond the size of the file,
    * then all strings have been processed, and the insertion is complete. 
    */   
   if(buffer - buffer_start >= input_file_size) goto insertion_complete;
   goto time_loop_insert;

   insertion_complete:

   /* stop the insertion timer */
   gettimeofday(&stop, NULL);

   /* do the math to compute the time required for insertion */   
   insert_real_time = 1000.0 * ( stop.tv_sec - start.tv_sec ) + 0.001  
   * (stop.tv_usec - start.tv_usec );
   insert_real_time = insert_real_time/1000.0;

   /* free the temp buffer used to store the file in memory */
   free(buffer_start);
   
   /* return the elapsed insertion time */
   return insert_real_time;
}

/* access the data structure to search for the strings found in the 
 * filename that is provided as a parameter. The file supplied must
 * be smaller than 2GB in size, otherwise, the code below has to be
 * modified to support large files, i.e., open64(), lseek64().
 * This should not be required, however, since the caller to this
 * function should be designed to handle multiple files, to allow you 
 * to break a large file into smaller pieces.  
 */
double perform_search(char *to_search)
{
   int32_t  input_file=0;
   int32_t  return_value=0;
   uint32_t input_file_size=0;
   uint32_t read_in_so_far=0;

   char *buffer=0;
   char *buffer_start=0;
   
   timer start, stop;
   double search_real_time=0.0;

   /* attempt to open the file for reading */
   if( (input_file=(int32_t)open (to_search, O_RDONLY)) <= 0 ) fatal(BAD_INPUT); 
   
   /* get the size of the file */  
   input_file_size=lseek(input_file, 0, SEEK_END);

   /* create a buffer to match the size of the file */
   if( (buffer = (char *)calloc(1, input_file_size+1 )) == NULL) 
     fatal(MEMORY_EXHAUSTED);
     
   /* read the file into memory */
   buffer_start=buffer;
   lseek(input_file, 0, SEEK_SET);

   /* attempt to read the entire file into memory */
   while(read_in_so_far < input_file_size)
   {
     return_value=read(input_file, buffer, input_file_size);
     assert(return_value>=0);
     read_in_so_far+=return_value;
   }
   close(input_file);
   
   /* make sure each string is null terminated */
   set_terminator(buffer, input_file_size); 
 
   /* start the timer for search */
   gettimeofday(&start, NULL);
   
   time_loop_search: 
 
   /* search for the first null terminated string in the buffer */
   if(search(buffer))  
   {
     _found++;
   }
   total_searched++;

   /* point to the next string in the buffer */
   for(; *buffer != '\0'; buffer++);
   buffer++;
   
   /* if the buffer pointer is incremented to beyond the size of the file,
    * then all strings have been processed 
    */
   if(buffer - buffer_start >= input_file_size) goto search_complete;
   goto time_loop_search;
   
   search_complete:
   
   /* stop the search timer */
   gettimeofday(&stop, NULL);
 
   /* do the math to compute the total time required for search */
   search_real_time = 1000.0 * ( stop.tv_sec - start.tv_sec ) + 0.001  
   * (stop.tv_usec - start.tv_usec );
   search_real_time = search_real_time/1000.0;
  
   /* free the file buffer */
   free(buffer_start);

   /* return the elapsed search time */
   return search_real_time;
}
