/*
 * Copyright (c) 1999-2001
 *      The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 */
/* A (growable) hash table */

typedef struct refhash_table
{
  __rcinfo **elements;
  unsigned long size, used;
} *refhash_table;

typedef struct
{
  refhash_table h;
  int index;
} refhash_scan;

static unsigned long ptr_hash(void *ptr)
{
  return (uintptr_t)ptr >> __HS_RCLOG;
}

#ifdef HASH_STATS

unsigned long total_elements_used, total_used, total_size;
unsigned long chain_squares;
unsigned max_chain, chains[33];

static void update_quality(refhash_table h)
{
  unsigned long i, elements_used = 0, l;
  __rcinfo *entry;

  for (i = 0; i < h->size; i++)
    if (h->elements[i])
      {
	elements_used++;
	for (l = 0, entry = h->elements[i]; entry; entry = entry->next)
	  l++;
	if (l > max_chain)
	  max_chain = l;
	chain_squares += l * l;
	if (l > 32)
	  l = 32;
	chains[l]++;
      }
    else
      chains[0]++;

  total_size += h->size;
  total_used += h->used;
  total_elements_used += elements_used;
}

__attribute__((destructor)) static void hashtable_report(void)
{
  double cmean;
  int i;

  mprintf("size %lu, used %lu, elements_used %lu\n",
	  total_size, total_used, total_elements_used);
  mprintf("max chain %u\n", max_chain);
  cmean = (double)total_used / total_elements_used;
  mprintf("chain mean %.2f, chain variance %.2f\n",
	  cmean, (double)chain_squares / total_elements_used - cmean * cmean);
  for (i = 0; i < 32; i++)
    mprintf("  chain %d = %u\n", i, chains[i]);
  mprintf("  chain >32 = %u\n", chains[32]);
}

#else
static void update_quality(refhash_table h) { }
#endif


static void rhclear(refhash_table h)
{
  unsigned long from = 0, count = h->size;

  while (count-- > 0)
    h->elements[from++] = NULL;
}

static refhash_table rhnew(unsigned long initial_size)
{
  refhash_table h = dlmalloc(sizeof(struct refhash_table));

  h->elements = dlmalloc(sizeof(void *) * initial_size);
  h->size = initial_size;
  h->used = 0;
  rhclear(h);

  return h;
}

static void rhfree(refhash_table h)
{
  dlfree(h->elements);
  dlfree(h);
}

static unsigned long rhused(refhash_table h)
{
  return h->used;
}

static __rcinfo *rhlookup(refhash_table h, void *ptr, int del)
{
  unsigned long hash = ptr_hash(ptr);
  unsigned long i = hash & (h->size - 1);
  __rcinfo **list = &h->elements[i], *entry;

  while ((entry = *list))
    {
      if (entry->from == ptr)
	{
	  if (del)
	    {
	      *list = entry->next;
	      h->used--;
	    }
	  return entry;
	}
      list = &entry->next;
    }
  return NULL;
}

static __rcinfo *rhlookup_range(refhash_table h, void *s, void *e, int del)
{
  /* Lookup a value in the s .. e range. We could try to be smart (only look
     in relevant buckets), but for now we just scan the whole table. */
  unsigned long i;

  for (i = 0; i < h->size; i++)
    {
      __rcinfo **list = &h->elements[i], *entry;

      while ((entry = *list))
	{
	  if (entry->from >= s && entry->from <= e)
	    {
	      if (del)
		{
		  *list = entry->next;
		  h->used--;
		}
	      return entry;
	    }
	  list = &entry->next;
	}
    }
  return NULL;
}

static void rhgrow(refhash_table h)
{
  __rcinfo **oldelements = h->elements;
  unsigned long j, oldsize = h->size;
  __rcinfo *entry, *next;

  update_quality(h);

  /* Grow hashtable */
  h->size *= 2;
  h->elements = dlmalloc(sizeof(void *) * h->size);
  rhclear(h);

  /* Rehash old entries */
  for (j = 0; j < oldsize; j++)
    for (entry = oldelements[j]; entry; entry = next)
      {
	unsigned long newhash = ptr_hash(entry->from);
	unsigned long newi = newhash & (h->size - 1);
		    
	next = entry->next;
	entry->next = h->elements[newi];
	h->elements[newi] = entry;
      }
  dlfree(oldelements);
}

void rhadd(refhash_table h, __rcinfo *x)
{
  unsigned long hash = ptr_hash(x->from);
  unsigned long i;

  h->used++;
  if (h->used >= 7 * h->size / 8)
    rhgrow(h);

  i = hash & (h->size - 1);
  x->next = h->elements[i];
  h->elements[i] = x;
}

#if 0
refhash_scan rhscan(refhash_table h)
{
  refhash_scan iterator;

  iterator.h = h;
  iterator.index = 0;

  return iterator;
}

void *rhnext(refhash_scan *iterator)
{
  refhash_table h = iterator->h;

  for (;;)
    {
      void *x;

      if (iterator->index >= h->size)
	return NULL;
      x = h->elements[iterator->index++];
      if (x)
	return x;
    }
}
#endif
