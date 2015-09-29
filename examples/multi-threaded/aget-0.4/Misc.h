
/*
 *
 * Multithreaded HTTP Download Accelarator: Aget
 * (c) 2002, Murat Balaban <murat@enderunix.org>
 *
 * See COPYING for copyright and copying restrictions
 *
 */

#ifndef MISC_H
#define MISC_H

#include "Data.h"

#define	LOGSIZ	1024

int calc_offset(int, int, int);
int numofthreads(int);
void parse_url(char *NTS, struct request *);
void usage();
void revstr(char *NTS);				/* Reverse String				*/
void Log(char *NTS, ...);			/* Log 						*/
void updateProgressBar(float, float);
void handleHttpRetcode(char *NTS);

time_t  t_start, t_finish;

#endif

