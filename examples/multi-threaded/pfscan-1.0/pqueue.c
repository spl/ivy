/*
** pqueue.c - FIFO queue management routines.
**
** Copyright (c) 1997-2002 Peter Eriksson <pen@lysator.liu.se>
**
** This program is free software; you can redistribute it and/or
** modify it as you wish - as long as you don't claim that you wrote
** it.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
*/


#include <stdlib.h>
#include <pthread.h>

#include <sharc/sharc.h>

#include "pqueue.h"

int
pqueue_init(PQUEUE *qp,
	   int qsize)
{
    qp->qsize = qsize;
    qp->buf = calloc(sizeof(char *), qsize);
    if (qp->buf == NULL)
	return 0;

    qp->occupied = 0;
    qp->nextin = 0;
    qp->nextout = 0;
    qp->closed = 0;

    pthread_mutex_init(&qp->mtx, NULL);
    pthread_cond_init(&qp->more, NULL);
    pthread_cond_init(&qp->less, NULL);

    return 0;
}



void
pqueue_close(PQUEUE *qp)
{
    pthread_mutex_lock(&qp->mtx);

    qp->closed = 1;

    pthread_mutex_unlock(&qp->mtx);
    pthread_cond_broadcast(&qp->more);
}


int
pqueue_put(PQUEUE *qp,
	   char *item)
{
    pthread_mutex_lock(&qp->mtx);

    if (qp->closed)
	return 0;
    
    while (qp->occupied >= qp->qsize)
	pthread_cond_wait(&qp->less, &qp->mtx);

    {
      char SLOCKED(&qp->mtx)* tmp;
      tmp = SCAST(item);
      qp->buf[qp->nextin++] = tmp;
    }

    qp->nextin %= qp->qsize;
    qp->occupied++;

    pthread_mutex_unlock(&qp->mtx);
    pthread_cond_signal(&qp->more);

    return 1;
}



int
pqueue_get(PQUEUE *qp,
	   char **item)
{
    int got = 0;

    
    pthread_mutex_lock(&qp->mtx);
    
    while (qp->occupied <= 0 && !qp->closed)
	pthread_cond_wait(&qp->more, &qp->mtx);

    if (qp->occupied > 0)
    {
	{
	  char SPRIVATE* tmp;
	  char SLOCKED(&qp->mtx)* tmp2 = qp->buf[qp->nextout];
	  qp->buf[qp->nextout++] = NULL;
	  tmp = SCAST(tmp2);
	  *item = tmp;
        }
	qp->nextout %= qp->qsize;
	qp->occupied--;
	got = 1;

	pthread_mutex_unlock(&qp->mtx);
	pthread_cond_signal(&qp->less);
    }
    else
	pthread_mutex_unlock(&qp->mtx);

    return got;
}



void
pqueue_destroy(PQUEUE *qp)
{
    pthread_mutex_destroy(&qp->mtx);
    pthread_cond_destroy(&qp->more);
    pthread_cond_destroy(&qp->less);
    free(qp->buf);
}
