#ifndef DATA_H
#define DATA_H

#include <pthread.h>
#include <netinet/in.h>

#include "Defs.h"

typedef struct request {
	char (NT host)[MAXHOSTSIZ];		/* Remote host	*/
	char (NT url)[MAXURLSIZ];		/* URL		*/
	char (NT file)[MAXBUFSIZ];		/* file name	*/
	char (NT lfile)[MAXBUFSIZ];		/* if local file name is specified	*/
	char (NT ip)[MAXIPSIZ+1];		/* Remote IP	*/
	char (NT username)[MAXBUFSIZ];	
	char (NT password)[MAXBUFSIZ];
	int port;
	int clength;			/* Content-length	*/
	unsigned char proto;		/* Protocol		*/
} request;

typedef struct thread_data {
	struct sockaddr_in sin;
	char (NT getstr)[GETREQSIZ+1];
	long soffset;		/* Start offset		*/
	long foffset;		/* Finish offset	*/
	long offset;		/* Current Offset	*/
	long clength;		/* Content Length	*/
	int fd;
	char padding1[64]; //zra
	pthread_t tid;		/* Thread ID		*/
	char padding2[64]; //zra
	unsigned char status;	/* thread exit status	*/
} thread_data;

#endif
