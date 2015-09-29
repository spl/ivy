/*
** pqueue.h - FIFO queue management routines.
**
** Copyright (c) 1997-2000 Peter Eriksson <pen@lysator.liu.se>
**
** This program is free software; you can redistribute it and/or
** modify it as you wish - as long as you don't claim that you wrote
** it.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
*/

#ifndef PLIB_PQUEUE_H
#define PLIB_PQUEUE_H

#include <sharc/sharc.h>

typedef struct
{
    char *NTS *COUNT(qsize) SLOCKED(&mtx) buf;
    int SLOCKED(&mtx) qsize;
    int SLOCKED(&mtx) occupied;
    int SLOCKED(&mtx) nextin;
    int SLOCKED(&mtx) nextout;
    int SLOCKED(&mtx) closed;
    pthread_mutex_t SRACY mtx;
    pthread_cond_t SRACY more;
    pthread_cond_t SRACY less;
} PQUEUE;


extern int
pqueue_init(PQUEUE *bp,
	   int qsize);

extern void
pqueue_destroy(PQUEUE *bp);

extern int
pqueue_put(PQUEUE *bp,
	  char *NTS item);

extern int
pqueue_get(PQUEUE *bp,
	   char *NTS *item);

extern void
pqueue_close(PQUEUE *bp);

#endif
    
