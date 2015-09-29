#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#include <sharCops.h>
#include "sharc_internals.h"

static int shortlog = 1;
static char *logfile;

#include "../heapsafe-lib/mprintf.c"

extern void *dlmalloc(size_t);
extern void dlfree(void *);

unsigned char __sharc_acc_table[ACC_TABLE_SIZE];
unsigned int __sharc_num_threads;
unsigned long conflicts;

#ifdef __APPLE__
/* No __thread */
pthread_key_t __this_sharc_thread_key;
#define SHARC_THREAD_INIT() (pthread_key_create(&__this_sharc_thread_key, NULL))

#else

__thread struct sharC_thread *__this_sharc_thread;

#define SHARC_THREAD_INIT()
#endif

pthread_mutex_t sharC_thread_list_mutex = PTHREAD_MUTEX_INITIALIZER;
struct sharC_thread *sharc_thread_list_head = NULL;

volatile char __sharc_pausing;

unsigned int __sharc_next_tid = 1;

/*
 * Runtime option handling
 */

static void parse_options(void)
{
  char *opts = getenv("SHARC"), *token;

  while ((token = strtok(opts, " "))) {
      opts = NULL;

      if (!strncmp(token, "logfile=", 8)) {
	  shortlog = 0;
	  logfile = token + 8;
      }
    }
}

void __sharc_thread_init(void)
{
    struct sharC_thread *this_sharc_thread = dlmalloc(sizeof(struct sharC_thread));

    SET_SHARC_THREAD(this_sharc_thread);
    //THIS_TID = pthread_self();
    THIS_READERIN = dlmalloc(READERIN_TABLE_SIZE);
    THIS_READ_LOG = dlmalloc(SHARC_LOG_SIZE);
    THIS_READ_LOGEND = THIS_READ_LOG;
    THIS_READMSG_LOG = dlmalloc(SHARC_LOG_SIZE);
    THIS_READMSG_LOGEND = THIS_READMSG_LOG;
    THIS_WRITE_LOG = dlmalloc(SHARC_LOG_SIZE);
    THIS_WRITE_LOGEND = THIS_WRITE_LOG;
    THIS_WRITEMSG_LOG = dlmalloc(SHARC_LOG_SIZE);
    THIS_WRITEMSG_LOGEND = THIS_WRITEMSG_LOG;

    THIS_MAX_LOCK = 0;
    THIS_BAR_LIST = NULL;

    /* add to list */
    pthread_mutex_lock(&sharC_thread_list_mutex);
    THIS_TID = __sharc_next_tid;
    if (!shortlog) {
	mprintf("SHARC: thread init(%p,%d)\n",
		this_sharc_thread,__sharc_next_tid);
	mprintf("SHARC: readerintable(%p,%p)\n",
		THIS_READERIN,THIS_READERIN+READERIN_TABLE_SIZE);
    }
    __sharc_next_tid++;
    this_sharc_thread->next = sharc_thread_list_head;
    this_sharc_thread->prev = NULL;
    sharc_thread_list_head = this_sharc_thread;
    if (sharc_thread_list_head->next)
        sharc_thread_list_head->next->prev = sharc_thread_list_head;
    __sharc_num_threads++;
    pthread_mutex_unlock(&sharC_thread_list_mutex);
}

void __sharc_thread_destroy(void)
{
    struct sharC_thread *this_sharc_thread = GET_SHARC_THREAD();
    struct sharC_barrier *tmp;

    pthread_mutex_lock(&sharC_thread_list_mutex);
    if (!shortlog) 
	mprintf("SHARC: thread destroy %d\n",THIS_TID);
    if (this_sharc_thread->prev)
        this_sharc_thread->prev->next = this_sharc_thread->next;
    if (this_sharc_thread->next)
        this_sharc_thread->next->prev = this_sharc_thread->prev;
    if (this_sharc_thread == sharc_thread_list_head)
        sharc_thread_list_head = this_sharc_thread->next;
    __sharc_num_threads--;
    pthread_mutex_unlock(&sharC_thread_list_mutex);

    __sharc_total_pause(); /* release things the thread has touched */
    dlfree(THIS_READERIN);
    dlfree(THIS_READ_LOG);
    dlfree(THIS_READMSG_LOG);
    dlfree(THIS_WRITE_LOG);
    dlfree(THIS_WRITEMSG_LOG);

    tmp = THIS_BAR_LIST;
    while (tmp) {
        struct sharC_barrier *nxt = tmp->next;
        __sharc_bar_destroy(tmp);
        tmp = nxt;
    }

    dlfree(this_sharc_thread);
    this_sharc_thread = NULL;
    SET_SHARC_THREAD(NULL);
}

__attribute__((constructor)) void __sharc_init_system()
{
    dlmalloc(1);
    parse_options();
    mprintf_init();

    __sharc_num_threads = 0;
    SHARC_THREAD_INIT();
    SET_SHARC_THREAD(NULL);
    __sharc_pausing = 0;

    __sharc_thread_init();
}

__attribute__((destructor)) static void __sharc_exit_system(void)
{
    memerr = 2; /* send summary to stderr */
    if (!shortlog || conflicts) {
	mprintf("%lu sharing errors\n", conflicts);
    }
}

void __sharc_error_read(void *addr, char owner, int who, char *confmsg, char *wrmsg)
{
    if (!shortlog)
	mprintf("SHARC: read conflict(%p):\n\twho(%d) %s\n\tlast(%d) %s\n",
		addr, who, confmsg, owner, wrmsg);
    conflicts++;
}

void __sharc_error_write(void *addr, char owner, int who, char *confmsg, char *msg)
{
    if (!shortlog)
	mprintf("SHARC: write conflict(%p):\n\twho(%d) %s\n\tlast(%d) %s\n",
		addr, who, confmsg, owner, msg);
    conflicts++;
}

void __sharc_lock_error(const void *lck,const void *what,unsigned int sz, char *msg)
{
    if (!shortlog)
	mprintf("SHARC: the lock at %p was not held for (%p, %d): %s\n",
		lck, what, sz, msg);
    conflicts++;
}

void __sharc_lock_coerce_error(void *dstlck,void *srclck,char *msg)
{
    if (!shortlog)
	mprintf("SHARC: the locks in the coercion at %s must be the same\n",
		msg);
    conflicts++;
}

void __sharc_cast_error(void *addr, unsigned long sz, char *msg)
{
    if (!shortlog)
	mprintf("SHARC: Invalid sharing cast. More than one reference to (%p,%lu): %s\n",
		addr, sz, msg);
    conflicts++;
}

void __sharc_error_single_threaded(char *msg)
{
    if (!shortlog)
	mprintf("SHARC: Non-single-threaded SINIT of SREADONLY at %s\n",
		msg);
    conflicts++;
}

void __sharc_log_read(void *addr,unsigned int who,unsigned char old, void *rina, unsigned char readerin)
{
    if (!shortlog)
	mprintf("SHARC: READ at %p by %d. old = %d. readerin(%p) = %d\n",
		addr,who,old,rina,readerin);
}

void __sharc_log_write(void *addr,unsigned int who,unsigned char old, void *rina, unsigned char readerin)
{
    if (!shortlog)
	mprintf("SHARC: WRITE at %p by %d. old = %d. readerin(%p) = %d\n",
		addr,who,old,rina,readerin);
}

/*
 * For SDYNBAR
 */

struct sharC_barrier *__sharc_bar_new(void *addr)
{
    struct sharC_barrier *n = dlmalloc(sizeof(struct sharC_barrier));

    n->next = (void *)0;
    n->baraddr = addr;
    n->read_log = dlmalloc(SHARC_LOG_SIZE);
    n->read_log_end = n->read_log;
    n->read_msg_log = dlmalloc(SHARC_LOG_SIZE);
    n->read_msg_log_end = n->read_msg_log;
    n->write_log = dlmalloc(SHARC_LOG_SIZE);
    n->write_log_end = n->write_log;
    n->write_msg_log = dlmalloc(SHARC_LOG_SIZE);
    n->write_msg_log_end = n->write_msg_log;

    return n;
}

void __sharc_bar_destroy(struct sharC_barrier *d)
{
    dlfree(d->read_log);
    dlfree(d->read_msg_log);
    dlfree(d->write_log);
    dlfree(d->write_msg_log);
    dlfree(d);
}

void __sharc_dynbar_coerce_error(void *dst, void *src, char *msg)
{
    if (!shortlog)
	mprintf("SHARC: the barriers in the coercion at %s must be the same\n",
		msg);
    conflicts++;
}
