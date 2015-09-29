/*
 * pthread_wrapper.c
 *
 * The stuff in this file provides wrappers for the pthread functions
 * that handle initialization for concurrent heapsafe and sharc.
 *
 * Zach Anderson(zra@cs.berkeley.edu)
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <dlfcn.h>
#include <pthread.h>

#include "sharc_internals.h"
#include "../heapsafe-lib/heapsafe_internals.h"

static int (*pthread_create_orig)(pthread_t *__restrict,
                                  __const pthread_attr_t *__restrict,
                                  void *(*)(void *),
                                  void *__restrict) = NULL;

__attribute__((__noreturn__)) static int (*pthread_exit_orig)(void *__retval) = NULL;

static void *checked_dlsym(void *handle, const char *sym)
{
    void *res = dlsym(handle,sym);
    if(res == NULL) {
        char *error = dlerror();
        if(error == NULL) {
            error = "checked_dlsym: sym is NULL";
        }
        fprintf(stderr, "checked_dlsym: %s\n", error);
        exit(-1);
    }
    return res;
}

__attribute__((constructor)) static void pthread_wrapper_init(void)
{

    pthread_create_orig = checked_dlsym(RTLD_NEXT, "pthread_create");
    pthread_exit_orig = checked_dlsym(RTLD_NEXT, "pthread_exit");

}

struct pthread_closure
{
    void *(*fn)(void *);
    void *arg;
};

static void *thread_func_wrapper(void *arg)
{
    struct pthread_closure *ac = (struct pthread_closure *)arg;
    struct pthread_closure c = {.fn = ac->fn, .arg = ac->arg};
    void *res;

    heapsafe_thread_init();
    __sharc_thread_init();

    dlfree(ac);
    res = c.fn(c.arg);

    __sharc_thread_destroy();
    heapsafe_thread_destroy();

    return res;
}

int pthread_create(pthread_t *__restrict thread,
                   __const pthread_attr_t *__restrict attr,
                   void * (*start_routine)(void *),
                   void *__restrict arg)
{
    struct pthread_closure *c = dlmalloc(sizeof(struct pthread_closure));
    int res;
    c->fn = start_routine;
    c->arg = arg;

    res = pthread_create_orig(thread,attr,&thread_func_wrapper,c);
    if (res != 0) dlfree(c);

    return res;
}

__attribute__((__noreturn__)) void pthread_exit(void *__retval)
{
    __sharc_thread_destroy();
    heapsafe_thread_destroy();

    pthread_exit_orig(__retval);
}
