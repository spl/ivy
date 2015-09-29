#ifndef HEAPSAFE_INTERNALS_H
#define HEAPSAFE_INTERNALS_H

void heapsafe_thread_init(void);
void heapsafe_thread_destroy(void);
void *dlmalloc(size_t size);
void dlfree(void *p);

#endif
