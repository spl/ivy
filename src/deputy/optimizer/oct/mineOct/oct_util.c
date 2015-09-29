/* oct_util.c
   Utilities functions not directly related to the abstract domain.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#include <oct.h>
#include <oct_private.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/time.h>
#include <unistd.h>

/**********/
/* Memory */
/**********/


/* this header is added before each block malloc'ed */
typedef struct
{
  size_t      size;      /* size of the block */

  mmalloc_t*  mm;        /* who monitor the block */
  int         id;        /* if id!=mm->id, monitor was reseted */

  double      dummy;     /* alignement stuff */

} mmheader_t;


/* global (default one at the begining */
static mmalloc_t  m_global = { 0,0,0,0,0,0,0 };
static mmalloc_t* mm_current = &m_global;
static mmalloc_t* mmalloc_global = &m_global;

#ifdef OCT_ENABLE_MALLOC_MONITORING
void*
OCT_PROTO(mm_malloc) (size_t t)
{ 
  char* m = (char*)malloc(t+sizeof(mmheader_t));
  mmheader_t* h = (mmheader_t*) m;
  if (!m) { fprintf(stderr, "Insufficent memory while attempting to allocate %i bytes in mm_malloc.",t); exit(1); }
  mm_current->nb_alloc++;
  mm_current->rem += t;
  mm_current->tot += t;
  if (mm_current->max < mm_current->rem) mm_current->max = mm_current->rem;
  h->mm = mm_current;
  h->size = t;
  h->id = mm_current->id;
  return m+sizeof(mmheader_t);
}

void*
OCT_PROTO(mm_realloc) (void* p, size_t t)
{
  char* m = ((char*)p)-sizeof(mmheader_t);
  mmheader_t* h = (mmheader_t*) m;
  size_t old_size = h->size;
  m = (char*)realloc(m,t+sizeof(mmheader_t));
  h = (mmheader_t*) m;
  if (!m) { fprintf(stderr, "Insufficent memory while attempting to reallocate %i bytes in mm_realloc.",t); exit(1); }
  if (h->id == h->mm->id) {
    h->mm->nb_realloc++;
    h->mm->tot += t-old_size;
    h->mm->rem += t-old_size;
    if (h->mm->max < h->mm->rem) h->mm->max = h->mm->rem;
  }
  h->size = t;
  return m+sizeof(mmheader_t);
}

void
OCT_PROTO(mm_free) (void* p)
{
  char* m = ((char*)p)-sizeof(mmheader_t);
  mmheader_t* h = (mmheader_t*) m;
  if (h->id == h->mm->id) {
    h->mm->nb_free++;
    h->mm->rem -= h->size;
  }
  free(m);
}
#endif

mmalloc_t*
OCT_PROTO(mmalloc_new) ()
{
  mmalloc_t* mm = new_t(mmalloc_t);
  mm->nb_alloc = mm->nb_realloc = mm->nb_free = 0;
  mm->rem = mm->max = mm->tot = 0;
  mm->id = 0;
  return mm;
}

void
OCT_PROTO(mmalloc_print) (mmalloc_t* mm)
{
#ifdef OCT_ENABLE_MALLOC_MONITORING
  printf("%i allocs, %i frees, %i reallocs\n%lu total memory used\n%lu memory peak\n%lu still allocated\n",
	 mm->nb_alloc,
	 mm->nb_free,
	 mm->nb_realloc,
	 (unsigned long)mm->tot,
	 (unsigned long)mm->max,
	 (unsigned long)mm->rem);
#else
  printf("No memory information available; compile with the ENABLE_MALLOC_MONITORING symbol.\n");
#endif
  fflush(stdout);
}

void 
OCT_PROTO(mmalloc_use) (mmalloc_t* mm)
{
  mm_current = mm;
}

mmalloc_t*
OCT_PROTO(mmalloc_get_current) ()
{
  return mm_current;
}

void
OCT_PROTO(mmalloc_reset) (mmalloc_t* mm)
{
  mm->nb_alloc = mm->nb_realloc = mm->nb_free = 0;
  mm->rem = mm->max = mm->tot = 0;
  mm->id++;
}



/**********/
/* Chrono */
/**********/

void
inline
OCT_PROTO(chrono_reset) (chrono_t* c)
{
  c->usec = 0;
  c->sec = 0;
  c->start = 0;
}

void
inline
OCT_PROTO(chrono_start) (chrono_t* c)
{
  OCT_ASSERT(!c->start,"oct_chrono_start: chrono already started");
  gettimeofday(&c->begin, NULL);
  c->start = 1;
}

void
inline
OCT_PROTO(chrono_stop) (chrono_t* c)
{
  struct timeval end;
  OCT_ASSERT(c->start,"oct_chrono_stop: chrono already stoped");
  c->start = 0;
  gettimeofday(&end, NULL);
  c->usec += (end.tv_usec - c->begin.tv_usec + 1000000L) % (1000000L);
  c->sec += (end.tv_sec - c->begin.tv_sec);
  c->sec += (c->usec / 1000000L);
  c->usec %= 1000000L;
  if (end.tv_usec < c->begin.tv_usec) c->sec--;
}

void
inline
OCT_PROTO(chrono_get) (chrono_t* c, long* hour, long* min, long* sec, long *usec)
{
  int start;
  start = c->start;
  if (start) oct_chrono_stop (c);
  *usec = c->usec;
  *sec = c->sec;
  *min = *sec/60; *sec %= 60;
  *hour = *min/60; *min %= 60;
  if (start) oct_chrono_start (c);
}


void
OCT_PROTO(chrono_print) (chrono_t* c)
{
  long hour, min, sec, usec;
  oct_chrono_get (c, &hour, &min, &sec, &usec);
  if (hour) printf("%lih %02li'", hour, min);
  else if (min) printf("%02li' %02li''", min, sec);
  else printf("%02li.%03li''", sec, usec/1000);
  fflush(stdout);
}


/*************/
/* Profiling */
/*************/

struct timing_tt
{
  char*    name;

  int      count; /* count number */

  int      rec;   /* recursive call checking */

  chrono_t tcum;  /* time elapsed in context and called context */
  chrono_t tself; /* time elapsed in this context, not in called context */

  struct timing_tt* stack; /* link to calling context */
};

typedef struct timing_tt timing_t;

static 
timing_t* timing_data[128] = {
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,
  NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL };

/* current context */
static 
timing_t* timing_stack = NULL;

/* keys are supposed to be < 64 and unique given a name */
void
OCT_PROTO(timing_enter) (const char* name, unsigned key)
{
  timing_t* t;
  OCT_ASSERT(key<sizeof(timing_data)/sizeof(timing_data[0]),
	     "oct_timing_enter: invalid key");
  t = timing_data[key];
  if (!t) {
    t = new_t(timing_t);
    t->name = strdup(name);
    t->count = 0;
    t->rec = 0;
    oct_chrono_reset(&(t->tcum));
    oct_chrono_reset(&(t->tself));
    timing_data[key] = t;
  }
  OCT_ASSERT(!t->rec,"oct_timing_enter: recursive call detected");
  t->count++;
  t->rec = 1;
  oct_chrono_start(&(t->tcum));
  oct_chrono_start(&(t->tself));
  if (timing_stack) oct_chrono_stop(&(timing_stack->tself));
  t->stack = timing_stack;
  timing_stack = t;
}

void
OCT_PROTO(timing_exit) (const char* name, unsigned key)
{
  timing_t* t;
  OCT_ASSERT(key<sizeof(timing_data)/sizeof(timing_data[0]),
	     "oct_timing_exit: invalid key");
  t = timing_data[key]; 
  OCT_ASSERT(t,"oct_timing_exit: invalid key");
  OCT_ASSERT(t->rec || timing_stack!=t,"oct_timing_exit: exiting an invalid context");
  timing_stack = t->stack;
  t->rec = 0;
  if (timing_stack) oct_chrono_start(&(timing_stack->tself));
  oct_chrono_stop(&(t->tself));
  oct_chrono_stop(&(t->tcum));
}

void
OCT_PROTO(timing_print) (const char* name)
{
#ifdef OCT_ENABLE_TIMING
  int i;
  timing_t* t = NULL;
  for (i=0;i<sizeof(timing_data)/sizeof(timing_data[0]);i++)
    if (timing_data[i] && !strcmp(timing_data[i]->name,name)) t=timing_data[i];
  if (!t) printf("No timing information for function %s.\n",name);
  else {
    printf("%-30s called=%9i time=",t->name,t->count);
    oct_chrono_print(&(t->tself));
    printf(" (cum=");
    oct_chrono_print(&(t->tcum));
    printf(")\n");
  }
#else
  printf("No timing information available; compile with the ENABLE_TIMING symbol.\n");
#endif
  fflush(stdout);
}

void
OCT_PROTO(timing_print_all) ()
{
#ifdef OCT_ENABLE_TIMING
  int i;
  for (i=0;i<sizeof(timing_data)/sizeof(timing_data[0]);i++) {
    timing_t* t = timing_data[i];
    if (t) {
      printf("%-30s called=%9i time=",t->name,t->count);
      oct_chrono_print(&(t->tself));
      printf(" (cum=");
      oct_chrono_print(&(t->tcum));
      printf(")\n");      
    }
  }
#else
  printf("No timing information available; compile with the ENABLE_TIMING symbol.\n");
#endif
  fflush(stdout);
}

void
OCT_PROTO(timing_reset) (const char* name)
{
  int i;
  timing_t* t = NULL;
  for (i=0;i<sizeof(timing_data)/sizeof(timing_data[0]);i++)
    if (timing_data[i] && !strcmp(timing_data[i]->name,name)) t=timing_data[i];
  if (t) {
    t->count = 0;
    oct_chrono_reset(&(t->tcum));
    oct_chrono_reset(&(t->tself));
    if (t->rec) {
      oct_chrono_start (&(t->tcum));
      if (timing_stack==t) oct_chrono_start (&(t->tself));
    }
  }
}

void
OCT_PROTO(timing_reset_all) ()
{
  int i;
  for (i=0;i<sizeof(timing_data)/sizeof(timing_data[0]);i++) {
    timing_t* t = timing_data[i];
    if (t) {
      t->count = 0;
      oct_chrono_reset(&(t->tcum));
      oct_chrono_reset(&(t->tself));
      if (t->rec) {
	oct_chrono_start (&(t->tcum));
	if (timing_stack==t) oct_chrono_start (&(t->tself));
      }
    }
  }
}

void
OCT_PROTO(timing_clear) ()
{
  int i;
  for (i=0;i<sizeof(timing_data)/sizeof(timing_data[0]);i++) {
    timing_t* t = timing_data[i];
    if (t) {
      OCT_ASSERT(!t->rec,"oct_timing_clear: not all contextes where closed");
      free (t->name);
      oct_mm_free (t);
    }
  }
}
