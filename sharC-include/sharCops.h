#define LOCK_PREFIX "lock;"

#define SINLINE inline

struct __sharc_xchg_dummy { unsigned long a[100]; };
#define __xg(x) ((struct __sharc_xchg_dummy *)(x))


static SINLINE unsigned long
__cmpxchgb(volatile void *ptr, unsigned char old, unsigned char new)
{
	unsigned long prev;
		__asm__ __volatile__(LOCK_PREFIX "cmpxchgb %b1,%2"
				     : "=a"(prev)
				     : "q"(new), "m"(*__xg(ptr)), "0"(old)
				     : "memory");
    return prev;
}

static SINLINE unsigned long
__cmpxchgl(volatile void *ptr, unsigned long old, unsigned long new)
{
	unsigned long prev;
		__asm__ __volatile__(LOCK_PREFIX "cmpxchgl %1,%2"
				     : "=a"(prev)
				     : "r"(new), "m"(*__xg(ptr)), "0"(old)
				     : "memory");
    return prev;
}

/* word layout is 
 * bottom bit - read or write locked
 * top seven bits - number of reading threads */

/* ownership table, with one byte per 32 allocated bytes */
#define SHARC_SHIFT 6
#define ACC_TABLE_SIZE (((unsigned long)(~0) >> SHARC_SHIFT) + 1)
extern unsigned char __sharc_acc_table[ACC_TABLE_SIZE];
#define SHARC_OWNER(p) \
    __sharc_acc_table[((unsigned long)p) >> SHARC_SHIFT]
#define SHARC_LOOKUP(p) SHARC_OWNER(p)

/* log of all things we took ownership of */
/* We allocate these big, and then rely on lazy page allocation and a page
 * wall at the end */
#define PAGE_SIZE 4096
#define PTRS_PER_PAGE ((PAGE_SIZE)/sizeof(unsigned char *))

#define SHARC_LOG_SIZE (4096*(PAGE_SIZE))
#define SHARC_LOG_ENTS ((PARCH_LOG_SIZE)/sizeof(unsigned char *))

struct sharC_barrier {
    struct sharC_barrier *next;
    void *baraddr;
    unsigned char **read_log,
                  **read_log_end;
    char **read_msg_log,
         **read_msg_log_end;
    unsigned char **write_log,
                  **write_log_end;
    char **write_msg_log,
         **write_msg_log_end;
};

struct sharC_thread {
    struct sharC_thread *next, *prev;

    unsigned int tid;

    /* bit array - set if this thread is a reader in
       the chunk */
    unsigned char *readerin;
#define READERIN_SHIFT (SHARC_SHIFT + 3)
#define READERIN_TABLE_SIZE (((unsigned long)(~0) >> READERIN_SHIFT) + 1)

    unsigned char **read_log, **read_log_end;
    char **read_msg_log, **read_msg_log_end;

    unsigned char **write_log, **write_log_end;
    char **write_msg_log, **write_msg_log_end;

#define SHARC_MAX_LOCKS 1000
    void *held_locks[SHARC_MAX_LOCKS];
    unsigned int max_lock;

    struct sharC_barrier *bar_list;
};

extern unsigned int __sharc_num_threads;
extern void __sharc_error_single_threaded(char *msg);
static SINLINE void __sharc_single_threaded(void *msg)
{
    if (__sharc_num_threads > 1)
        __sharc_error_single_threaded(msg);
    return;
}

#ifdef __APPLE__
/* This has to match apple's def - hopefully that won't change for a while */
typedef unsigned long __sharc_pthread_key_t;
int       pthread_setspecific(__sharc_pthread_key_t key,
			      const void *value);
void     *pthread_getspecific(__sharc_pthread_key_t key);

/* No __thread */
extern __sharc_pthread_key_t __this_sharc_thread_key;
#define SET_SHARC_THREAD(t) (pthread_setspecific(__this_sharc_thread_key, (t)))
#define GET_SHARC_THREAD() ((struct sharC_thread *)pthread_getspecific(__this_sharc_thread_key))

#else

extern __thread struct sharC_thread *__this_sharc_thread;

#define SET_SHARC_THREAD(t) (__this_sharc_thread = (t))
#define GET_SHARC_THREAD() __this_sharc_thread
#endif

extern struct sharC_thread *sharc_thread_list_head;

#define THREAD_TID(thread) ((thread)->tid)
#define THREAD_READERIN_ARR(thread) ((thread)->readerin)
#define THREAD_READ_LOG(thread) ((thread)->read_log)
#define THREAD_READ_LOGEND(thread) ((thread)->read_log_end)
#define THREAD_READMSG_LOG(thread) ((thread)->read_msg_log)
#define THREAD_READMSG_LOGEND(thread) ((thread)->read_msg_log_end)
#define THREAD_WRITE_LOG(thread) ((thread)->write_log)
#define THREAD_WRITE_LOGEND(thread) ((thread)->write_log_end)
#define THREAD_WRITEMSG_LOG(thread) ((thread)->write_msg_log)
#define THREAD_WRITEMSG_LOGEND(thread) ((thread)->write_msg_log_end)
#define THREAD_LOCKS(thread,i) ((thread)->held_locks[(i)])
#define THREAD_MAX_LOCK(thread) ((thread)->max_lock)
#define THREAD_BAR_LIST(thread) ((thread)->bar_list)
#define THREAD_READERIN(thread,x) (THREAD_READERIN_ARR((thread))[(unsigned long)(x)>>READERIN_SHIFT])
#define READERIN_BIT_IDX(x) (0x1 << (((unsigned long)(x)>>SHARC_SHIFT)&0x7))
#define IS_THREAD_READERIN(thread,x) (THREAD_READERIN((thread),(x)) & READERIN_BIT_IDX((x)))
#define SET_THREAD_READERIN(thread,x) (THREAD_READERIN((thread),(x)) |= READERIN_BIT_IDX((x)))
#define CLEAR_THREAD_READERIN(thread,x) (THREAD_READERIN((thread),(x)) &= ~READERIN_BIT_IDX((x)))
#define THREAD_RECORD_READ(thread,x) (*(THREAD_READ_LOGEND((thread)))++ = (&SHARC_OWNER((x))))
#define THREAD_RECORD_READMSG(thread,x) (*(THREAD_READMSG_LOGEND((thread)))++ = (x))
#define THREAD_RECORD_WRITE(thread,x) (*(THREAD_WRITE_LOGEND((thread)))++ = (&SHARC_OWNER((x))))
#define THREAD_RECORD_WRITEMSG(thread,x) (*(THREAD_WRITEMSG_LOGEND((thread)))++ = (x))

#define THIS_TID             (THREAD_TID((GET_SHARC_THREAD())))
#define THIS_READERIN        (THREAD_READERIN_ARR((GET_SHARC_THREAD())))
#define THIS_READ_LOG        (THREAD_READ_LOG((GET_SHARC_THREAD())))
#define THIS_READ_LOGEND     (THREAD_READ_LOGEND((GET_SHARC_THREAD())))
#define THIS_READMSG_LOG     (THREAD_READMSG_LOG((GET_SHARC_THREAD())))
#define THIS_READMSG_LOGEND  (THREAD_READMSG_LOGEND((GET_SHARC_THREAD())))
#define THIS_WRITE_LOG       (THREAD_WRITE_LOG((GET_SHARC_THREAD())))
#define THIS_WRITE_LOGEND    (THREAD_WRITE_LOGEND((GET_SHARC_THREAD())))
#define THIS_WRITEMSG_LOG    (THREAD_WRITEMSG_LOG((GET_SHARC_THREAD())))
#define THIS_WRITEMSG_LOGEND (THREAD_WRITEMSG_LOGEND((GET_SHARC_THREAD())))
#define THIS_LOCKS(i)        (THREAD_LOCKS((GET_SHARC_THREAD()),(i)))
#define THIS_MAX_LOCK        (THREAD_MAX_LOCK((GET_SHARC_THREAD())))
#define THIS_BAR_LIST        (THREAD_BAR_LIST((GET_SHARC_THREAD())))
#define READERIN(x)          (THREAD_READERIN((GET_SHARC_THREAD()),(x)))
#define IS_READERIN(x)       (IS_THREAD_READERIN((GET_SHARC_THREAD()),(x)))
#define SET_READERIN(x)      (SET_THREAD_READERIN((GET_SHARC_THREAD()),(x)))
#define CLEAR_READERIN(x)    (CLEAR_THREAD_READERIN((GET_SHARC_THREAD()),(x)))
#define RECORD_READ(x)       (THREAD_RECORD_READ((GET_SHARC_THREAD()),(x)))
#define RECORD_READMSG(x)    (THREAD_RECORD_READMSG((GET_SHARC_THREAD()),(x)))
#define RECORD_WRITE(x)      (THREAD_RECORD_WRITE((GET_SHARC_THREAD()),(x)))
#define RECORD_WRITEMSG(x)   (THREAD_RECORD_WRITEMSG((GET_SHARC_THREAD()),(x)))

extern void __sharc_init_system();
extern void __sharc_thread_init();


static SINLINE void __sharc_total_pause();

extern volatile char __sharc_pausing;
static SINLINE void __sharc_pause_begin()
{
    char old = __sharc_pausing;
    while (__cmpxchgb(&__sharc_pausing,old,1) == 1)
        old = __sharc_pausing;
}

static SINLINE void __sharc_pause_end()
{
    __sharc_pausing = 0;
}

static SINLINE void __sharc_pause_wait()
{
    while (__sharc_pausing == 1);
}

/* On a conflict, return the log message for one previous access.
 */
static SINLINE char *
__sharc_find_log_msg(void *addr)
{
    struct sharC_thread *tmp = sharc_thread_list_head;
    while (tmp) {
        if (IS_THREAD_READERIN(tmp,addr)) {
            unsigned char **readaddr = THREAD_READ_LOG(tmp);
            char **readmsg  = THREAD_READMSG_LOG(tmp);
            unsigned char **writeaddr = THREAD_WRITE_LOG(tmp);
            char **writemsg = THREAD_WRITEMSG_LOG(tmp);

            /* look in write log first */
            while (writeaddr < THREAD_WRITE_LOGEND(tmp)) {
                if (*writeaddr == &SHARC_OWNER(addr))
                    return *writemsg;
                writeaddr++;
                writemsg++;
            }

            /* now look in read log */
            while (readaddr < THREAD_READ_LOGEND(tmp)) {
                if (*readaddr == &SHARC_OWNER(addr))
                    return *readmsg;
                readaddr++;
                readmsg++;
            }

        }

        tmp = tmp->next;
    }

    return (char *)0;
}

extern void __sharc_error_read(void *addr, char owner, int who,
                               char *confmsg, char *wrmsg);

static SINLINE void
__sharc_construct_rerror(unsigned char *logent, char *confmsg, unsigned char old)
{
    unsigned int owner = old >> 1;
    char *oldmsg = __sharc_find_log_msg(logent);

    __sharc_error_read(logent,owner,THIS_TID,confmsg,oldmsg);
    return;
}

extern void __sharc_log_read(void *addr,unsigned int who,unsigned char old, 
                             void *rina, unsigned char readerin);

/* we want to read this address. Get permission to do this by setting 
 * our bit in the control word */
static SINLINE void __sharc_read(void* addr,char *msg){
    unsigned char old;

    if (!GET_SHARC_THREAD()) {
        __sharc_thread_init();
    }

    if (__sharc_num_threads == 1) {
        if (THIS_READ_LOGEND > THIS_READ_LOG)
            __sharc_total_pause();
        return;
    }

    __sharc_pause_wait(); /* wait for any pauses to finish */
    old = SHARC_LOOKUP(addr);

    if (IS_READERIN(addr)) {
        /* we have read already */
    } else if(old & 0x1) {
        /* someone else has a write lock */
        __sharc_construct_rerror(addr,msg,old);
    } else {
        unsigned char n = (old & 0x1) | (((old >> 1) + 1) << 1);
        while(__cmpxchgb(&SHARC_OWNER(addr),old,n) != old){
            old = SHARC_LOOKUP(addr);
            n = (old & 0x1) | (((old >> 1) + 1) << 1);
            if(old & 0x1){
                __sharc_construct_rerror(addr,msg,old);
            }
        };
        RECORD_READ(addr);
        RECORD_READMSG(msg);
        SET_READERIN(addr);
    }
}


extern void __sharc_error_write(void *addr, char owner, int who,
                                char *confmsg, char *msg);

static SINLINE void
__sharc_construct_werror(void *logent,char *confmsg,char old)
{
    char *oldmsg = __sharc_find_log_msg(logent);

    __sharc_error_write(logent,old,THIS_TID,confmsg,oldmsg);
    return;
}

void __sharc_log_write(void *addr,unsigned int who,unsigned char old, 
                       void *rina, unsigned char readerin);

static SINLINE void __sharc_write(void* addr,char *msg){
    unsigned char old;
    unsigned char others;
    unsigned char justme;
    unsigned char want;

    if (!GET_SHARC_THREAD()) {
        __sharc_thread_init();
    }

    if (__sharc_num_threads == 1) {
        if (THIS_READ_LOGEND > THIS_READ_LOG)
            __sharc_total_pause();
        return;
    }

    __sharc_pause_wait();
    old = SHARC_LOOKUP(addr);
    justme = (old >> 1) == 1 && (IS_READERIN(addr));
    others = (old >> 1) != 0 && !((old >> 1) == THIS_TID && (old & 0x1));
    want = 0x1 | (THIS_TID << 1);

    if (others && !justme){
        __sharc_construct_werror(addr,msg,old);
    } else if (old == want) {
        /* we have already locked it */
    } else {
        /** sometimes this returns the new value? how can it be?! */
        if (old != __cmpxchgb(&SHARC_OWNER(addr),old,want)){
            if (SHARC_OWNER(addr) != want) /* why do I have to do this??? */
                __sharc_construct_werror(addr,msg,SHARC_OWNER(addr));
            else {
                RECORD_WRITE(addr);
                RECORD_WRITEMSG(msg);
                SET_READERIN(addr);
            }
        } else {
            RECORD_WRITE(addr);
            RECORD_WRITEMSG(msg);
            SET_READERIN(addr);
        }
    }
}

static SINLINE void
__sharc_read_range(void *p, unsigned int sz, char *msg)
{
    unsigned int i;
    for (i = 0; i < sz; i += (1 << SHARC_SHIFT))
        __sharc_read(p + i, msg);
}

static SINLINE void
__sharc_write_range(void *p, unsigned int sz, char *msg)
{
    unsigned int i;
    for (i = 0; i < sz; i += (1 << SHARC_SHIFT)) {
        __sharc_write(p + i, msg);
    }
}

static SINLINE unsigned int __sharc_strlen(char *str)
{
    char *s;

    if (!str) return 0;

    for (s = str; *s; s++)
      ;
    return s - str;
}

static SINLINE void __sharc_partial_pause(unsigned int lo, unsigned int hi) {
    unsigned char *lop, *hip;
    unsigned char *pos;

    if (!lo || hi <= lo) return;

    lop = &SHARC_OWNER(lo);
    hip = &SHARC_OWNER(hi);

    __sharc_pause_begin();
    /* clear our read bit for all blocks we have read locks on */
    for (pos = lop; pos <= hip; pos++) {
        unsigned char old = *pos;

        if (old == (0x1 | (THIS_TID << 1))) { /* this thread has write lock */
            *pos = 0;
        }
        else if (IS_READERIN(lo + ((pos - lop)<<SHARC_SHIFT))) { /* this thread has read lock */
            while (old != __cmpxchgb(pos,old,(old & 1)|(((old>>1)-1)<<1)))
                old = *pos;
        }
    }

    __sharc_pause_end();
}

static SINLINE void __sharc_barrier_all_pause();

static SINLINE void __sharc_force_total_pause()
{
    unsigned char** pos;

    __sharc_pause_begin();

    /* clear our read bit for all blocks we have read locks on */
    for (pos = THIS_READ_LOG;
         pos < THIS_READ_LOGEND; pos++){
        unsigned char *addr = *pos;
        unsigned char old = *addr;

        while(old != __cmpxchgb(addr,old,(old & 1)|(((old>>1)-1)<<1))){
            old = *addr;
        }
    }
    THIS_READ_LOGEND = THIS_READ_LOG;
    THIS_READMSG_LOGEND = THIS_READMSG_LOG;

    /* clear ownership byte for all blocks we have exclusive locks on */
    for (pos = THIS_WRITE_LOG;
         pos < THIS_WRITE_LOGEND; pos++){
        unsigned char *addr = *pos;

        *addr = 0;
    }
    THIS_WRITE_LOGEND = THIS_WRITE_LOG;
    THIS_WRITEMSG_LOGEND = THIS_WRITEMSG_LOG;

    __sharc_barrier_all_pause();

    __sharc_pause_end();

}

static SINLINE void __sharc_total_pause()
{
    __sharc_force_total_pause();
}


extern void __sharc_lock_error(const void *lck,const void *what,unsigned int sz,
                               char *msg);
extern void __sharc_lock_coerce_error(void *dstlck,void *srclck,char *msg);

/* assumes no double-locking */
static SINLINE void
__sharc_add_lock(void *lck)
{
    unsigned int i;
    for (i = 0; i <= THIS_MAX_LOCK; i++)
        if (!THIS_LOCKS(i))
            break;

    if (i > THIS_MAX_LOCK && THIS_MAX_LOCK < SHARC_MAX_LOCKS)
            THIS_MAX_LOCK++;

    THIS_LOCKS(i) = lck;
    return;
}

/* this will be very inefficient if the lock isn't actually held */
static SINLINE void
__sharc_rm_lock(void *lck)
{
    unsigned int i;
    for (i = 0; i <= THIS_MAX_LOCK; i++)
        if (THIS_LOCKS(i) == lck)
            break;

    if (i == THIS_MAX_LOCK && THIS_MAX_LOCK > 0)
            THIS_MAX_LOCK--;

    THIS_LOCKS(i) = (void *)0;
    return;
}

static SINLINE void
__sharc_chk_lock(void *lck, void *what, unsigned int sz, char *msg)
{
    unsigned int i;

    if (__sharc_num_threads == 1) return;

    for (i = 0; i <= THIS_MAX_LOCK; i++)
        if (THIS_LOCKS(i) == lck)
            break;

    if (i > THIS_MAX_LOCK) {
            __sharc_lock_error(lck,what,sz,msg);
    }
}

static SINLINE void
__sharc_coerce_lock(void *dstlck, void *srclck, char *msg)
{
    if (dstlck != srclck)
        __sharc_lock_coerce_error(dstlck,srclck,msg);
}

/*
 * Instrumentation for SDYNBAR
 *
 */

static SINLINE struct sharC_barrier *
__sharc_bar_find(struct sharC_barrier *l, void *addr)
{
    while (l) {
        if (l->baraddr == addr) break;
        l = l->next;
    }

    return l;
}

extern struct sharC_barrier *__sharc_bar_new(void *addr);
extern void __sharc_bar_destroy(struct sharC_barrier *d);

static SINLINE void
__sharc_bar_add(struct sharC_barrier **head, struct sharC_barrier *n)
{
    struct sharC_barrier *tmp;

    if (!*head) {
        *head = n;
        return;
    }

    tmp = *head;
    while (tmp->next)
        tmp = tmp->next;

    tmp->next = n;
}

static SINLINE void
__sharc_bar_remove(struct sharC_barrier **head, void *baddr)
{
    struct sharC_barrier *tmp1, *tmp2;

    if (!*head) return;

    if ((*head)->baraddr == baddr) {
        *head = (*head)->next;
        return;
    }

    tmp1 = *head; tmp2 = (*head)->next;
    while (tmp2) {
        if (tmp2->baraddr == baddr) {
            tmp1->next = tmp2->next;
            return;
        }
        tmp1 = tmp2;
        tmp2 = tmp2->next;
    }
}

static SINLINE char *
__sharc_find_db_log_msg(void *bar, void *addr)
{
    struct sharC_thread *tmp = sharc_thread_list_head;
    struct sharC_barrier *thisbar;

    while (tmp) {
        if ((thisbar = __sharc_bar_find(THREAD_BAR_LIST(tmp),bar))) {
            if (IS_THREAD_READERIN(tmp,addr)) {
                unsigned char **readaddr = thisbar->read_log;
                char **readmsg  = thisbar->read_msg_log;
                unsigned char **writeaddr = thisbar->write_log;
                char **writemsg = thisbar->write_msg_log;

                /* look in write log first */
                while (writeaddr < thisbar->write_log_end) {
                    if (*writeaddr == &SHARC_OWNER(addr))
                        return *writemsg;
                    writeaddr++;
                    writemsg++;
                }

                /* now look in read log */
                while (readaddr < thisbar->read_log_end) {
                    if (*readaddr == &SHARC_OWNER(addr))
                        return *readmsg;
                    readaddr++;
                    readmsg++;
                }

            }
        }

        tmp = tmp->next;
    }

    return (char *)0;
}

static SINLINE void
__sharc_barrier_pause(struct sharC_barrier *b)
{
    unsigned char** pos;

    /* clear our read bit for all blocks we have read locks on */
    for (pos = b->read_log;
         pos < b->read_log_end; pos++){
        unsigned char *addr = *pos;
        unsigned char old = *addr;

        while(old != __cmpxchgb(addr,old,(old & 1)|(((old>>1)-1)<<1))){
            old = *addr;
        }
    }
    b->read_log_end = b->read_log;
    b->read_msg_log_end = b->read_msg_log;

    /* clear ownership byte for all blocks we have exclusive locks on */
    for (pos = b->write_log;
         pos < b->write_log_end; pos++){
        unsigned char *addr = *pos;

        *addr = 0;
    }
    b->write_log_end = b->write_log;
    b->write_msg_log_end = b->write_msg_log;

}

static SINLINE void
__sharc_barrier_all_pause()
{
    struct sharC_barrier *tmp = THIS_BAR_LIST;
    while (tmp) {
        __sharc_barrier_pause(tmp);
        tmp = tmp->next;
    }
}

static SINLINE void
__sharc_dynbar(void *bar)
{
    struct sharC_barrier *thisbar;

    if (__sharc_num_threads == 1) return;
    if (!(thisbar = __sharc_bar_find(THIS_BAR_LIST,bar))) return;

    __sharc_barrier_pause(thisbar);

}

static SINLINE void
__sharc_construct_dbrerror(void *bar,unsigned char *logent, char *confmsg, unsigned char old)
{
    unsigned int owner = old >> 1;
    char *oldmsg = __sharc_find_db_log_msg(bar,logent);

    __sharc_error_read(logent,owner,THIS_TID,confmsg,oldmsg);
    return;
}

static SINLINE void
__sharc_dynbar_read(void *bar, void *addr, char *msg)
{
    unsigned char old;
    struct sharC_barrier *thisbar;

    if (__sharc_num_threads == 1) return;

    if (!(thisbar = __sharc_bar_find(THIS_BAR_LIST,bar))) {
        thisbar = __sharc_bar_new(bar);
        __sharc_bar_add(&THIS_BAR_LIST, thisbar);
    }

    old = SHARC_LOOKUP(addr);

    if (IS_READERIN(addr)) {
        /* we have read already */
    } else if(old & 0x1) {
        /* someone else has a write lock */
        __sharc_construct_dbrerror(bar,addr,msg,old);
    } else {
        unsigned char n = (old & 0x1) | (((old >> 1) + 1) << 1);
        while(__cmpxchgb(&SHARC_OWNER(addr),old,n) != old){
            old = SHARC_LOOKUP(addr);
            n = (old & 0x1) | (((old >> 1) + 1) << 1);
            if(old & 0x1){
                __sharc_construct_dbrerror(bar,addr,msg,old);
            }
        }
        *(thisbar->read_log_end)++ = &SHARC_OWNER(addr);
        *(thisbar->read_msg_log_end)++ = msg;
        SET_READERIN(addr);
    }
}

static SINLINE void
__sharc_construct_dbwerror(void *bar,void *logent,char *confmsg,char old)
{
    //unsigned int owner = old >> 1;
    char *oldmsg = __sharc_find_db_log_msg(bar,logent);

    __sharc_error_write(logent,old,THIS_TID,confmsg,oldmsg);
    return;
}

static SINLINE void
__sharc_dynbar_write(void *bar, void *addr, char *msg)
{
    unsigned char old;
    unsigned char others;
    unsigned char justme;
    unsigned char want;
    struct sharC_barrier *thisbar;

    if (__sharc_num_threads == 1) return;

    if (!(thisbar = __sharc_bar_find(THIS_BAR_LIST,bar))) {
        thisbar = __sharc_bar_new(bar);
        __sharc_bar_add(&THIS_BAR_LIST, thisbar);
    }

    old = SHARC_LOOKUP(addr);
    justme = (old >> 1) == 1 && (IS_READERIN(addr));
    others = (old >> 1) != 0 && !((old >> 1) == THIS_TID && (old & 0x1));
    want = 0x1 | (THIS_TID << 1);

    if (others && !justme){
        __sharc_construct_dbwerror(bar,addr,msg,old);
    } else if (old == want) {
        /* we have already locked it */
    } else {
        /** sometimes this returns the new value? how can it be?! */
        if (old != __cmpxchgb(&SHARC_OWNER(addr),old,want)){
            if (SHARC_OWNER(addr) != want) /* why do I have to do this??? */
                __sharc_construct_dbwerror(bar,addr,msg,SHARC_OWNER(addr));
            else {
                *(thisbar->write_log_end)++ = &SHARC_OWNER(addr);
                *(thisbar->write_msg_log_end)++ = msg;
                //RECORD_WRITE(addr);
                //RECORD_WRITEMSG(msg);
                SET_READERIN(addr);
            }
        } else {
            *(thisbar->write_log_end)++ = &SHARC_OWNER(addr);
            *(thisbar->write_msg_log_end)++ = msg;
            //RECORD_WRITE(addr);
            //RECORD_WRITEMSG(msg);
            SET_READERIN(addr);
        }
    }
}

extern void __sharc_dynbar_coerce_error(void *dst, void *src, char *msg);

static SINLINE void
__sharc_coerce_dynbar(void *dst, void *src, char *msg)
{
    if (dst != src)
        __sharc_dynbar_coerce_error(dst,src,msg);
}

static SINLINE void
__sharc_dynbar_readrange(void *bar, void *p, unsigned int sz, char *msg)
{
    unsigned int i;
    for (i = 0; i < sz; i += (1 << SHARC_SHIFT))
        __sharc_dynbar_read(bar,p + i, msg);
}

static SINLINE void
__sharc_dynbar_writerange(void *bar, void *p, unsigned int sz, char *msg)
{
    unsigned int i;
    for (i = 0; i < sz; i += (1 << SHARC_SHIFT))
        __sharc_dynbar_write(bar,p + i, msg);
}


/*
 * The sharing cast.
 *
 */

#include <heapsafe/rcops.h>
extern long hs_refcount(const void *p, unsigned long s, unsigned int zero);
extern void __sharc_cast_error(void *addr, unsigned long sz, char *msg);
static inline void
__sharc_crc_adjust_ptr_void(void *x, int by, unsigned int  size, int inv)
{
  void **p = x;

  RC_ADJUST_START(p, size);
  if (inv) {
  CRC_INVALIDATE(&((*p)));
  } else {
  CRC_ADJUST(&((*p)),(by));
  }
  RC_ADJUST_END(p, sizeof *p);
}



static SINLINE void *
__sharc_sharing_cast(void *addr,void **slot, unsigned int localslot __attribute__((unused)),
                     unsigned long lo, unsigned long hi,
                     char *msg)
{
    int cnt;
    __builtin_hs_argnull();
    __builtin_hs_cpush(&slot);
    __builtin_hs_cpush(&addr);
    __builtin_hs_cpush(&msg);

    if (slot) {
        __builtin_hs_cadjust(__sharc_crc_adjust_ptr_void, slot, -1, 0, 0);
        *slot = (void *)0;
        __builtin_hs_cadjust(__sharc_crc_adjust_ptr_void, slot, 1, 0, 0);
        __builtin_hs_cpop(&slot);
    }
    else __builtin_hs_cpop(&slot);

    if (lo && (cnt = hs_refcount((void *)lo,(hi-lo)?(hi-lo):1,0)) != 1) {
      if (cnt < 1)
        __sharc_cast_error((void *)lo, (hi-lo)+1000000000, msg);
      else
        __sharc_cast_error((void *)lo, hi-lo, msg);
    }

    __builtin_hs_cpop(&msg);
    __builtin_hs_retpush(&addr);
    return addr;
}
