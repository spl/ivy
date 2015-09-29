int fprintf(void SRACY* stream, char *format, ...);

typedef void SRACY pthread_mutex_t;
typedef void SRACY pthread_cond_t;

#ifdef __APPLE__
int pthread_join(void *SREADS(sizeof(struct _opaque_pthread_t)), void *SWRITES(sizeof(void *)));
int pthread_cancel(void *SREADS(sizeof(struct _opaque_pthread_t)));
#endif

int pthread_cond_timedwait(void SRACY * __cond,
                           void SRACY * __mutex,
                           void SPRIVATE * __abstime);

int pthread_cond_init(void SRACY* __cond, void * __cond_attr);
int pthread_cond_signal (void SRACY * __cond);
int pthread_cond_broadcast (void SRACY * __cond);
int pthread_cond_destroy (void SRACY * __cond);

void pthread_mutex_init (void SRACY* __mutex, void *attrs);
void pthread_mutex_lock (void SRACY* __mutex);
void pthread_mutex_unlock (void SRACY * __mutex);
void pthread_mutex_destroy (void SRACY * __mutex);
int pthread_sigmask(int how, const void *SREADS(sizeof(sigset_t)) set, 
		    void *SWRITES(sizeof(sigset_t)) oset);
int sigwait(const void *SREADS(sizeof(sigset_t)) set, int *SWRITES(sizeof(int)) sig);

void (STCREATE(2,3) pthread_create)(void *SWRITES(1) tid, void *attr,
                                    void *(*fn)(void *),void * arg);

int __xstat(int __ver, char *SREADS(strlen(__filename)+1) __filename, void *__stat_buf);

int chmod(char *SREADS(strlen(path)+1) path, void mode);

int chown(char *SREADS(strlen(path)+1) path, void owner, void group);

int utime(char *SREADS(strlen(filename)+1) filename, void *buf);

unsigned int read(int fd, void *SWRITES(count) buf, void count);

unsigned int write(int fd, void *SREADS(count) buf, void count);

void strlen(char *SREADS(strlen(s)+1) s);

void *memcpy(void *SWRITES(n) dest, void *SREADS(n) src, void n);

int pthread_cond_wait(void SRACY * __cond, void SRACY * __mutex);

/* Standard library file operations lock the stream internally */
typedef void SRACY FILE;

void SRACY* stderr;
void SRACY* stdin;
void SRACY* stdout;

void SRACY*fopen(char *SREADS(strlen(path)+1) path, char *mode);
int fclose(void SRACY *fp);
long fwrite(void *SREADS(size*nmemb) ptr, long size, long nmemb, void SRACY* stream);
long fread(void *SWRITES(size*nmemb) ptr, long size, long nmemb, void SRACY* stream);
int vfprintf(void SRACY* stream, char *format, void ap);
int fflush(void SRACY* stream);
int fputs(const char *s, void SRACY* stream);
int fputc(int c, void SRACY * stream);
int putc(int c, void SRACY * stream);
int _IO_putc(int __c, void SRACY * __fp);
int fgetc(void SRACY * stream);
int _IO_getc(void SRACY * stream);
char *fgets(char *s, int size, void SRACY *stream);
int ungetc(int c, void SRACY * stream);

int open(char *SREADS(strlen(pathname)+1) pathname, int flags, ...);

char *strcpy(char *SWRITES(strlen(src)+1) dest, char *SREADS(strlen(src)+1) src);
char *__builtin_strncpy(char *SWRITES(n) dest, char *SREADS(n), unsigned int n);

void *memset(void *SWRITES(n) s, int c, void n);

int strncasecmp(char *SREADS(n) s1, char *SREADS(n) s2, void n);

char *strcat(char *SWRITES(strlen(dest)+strlen(src)+1) dest, char *SREADS(strlen(src)+1) src);

char *strncat(char *SWRITES(strlen(dest)+n+1) dest, char *SREADS(n) src, void n);

char *strncpy(char *SWRITES(n) dest, char *SREADS(n) src, void n);

int remove(char *SREADS(strlen(pathname)) pathname);

long __strtol_internal(char *SREADS(strlen(nptr) + 1) nptr, char **endptr, int base, int group);
