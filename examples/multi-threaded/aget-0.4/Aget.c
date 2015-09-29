
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/socket.h>

#include <netinet/in.h>

#include <arpa/inet.h>

#include <errno.h>

#include <sharc/sharc.h>

#include "Head.h"
#include "Aget.h"
#include "Misc.h"
#include "Download.h"
#include "Resume.h"
#include "Data.h"
#include "Signal.h"

extern int fsuggested;
extern int SREADONLY ASSUMECONST nthreads;
extern struct thread_data SDYNAMIC * COUNT(nthreads) SREADONLY wthread;
extern struct request *SAFE req;
extern int bwritten;
extern pthread_t hthread;

//extern int errno;


void get(struct request *req)
{
	struct thread_data SDYNAMIC* wthread_tmp;
	struct thread_data *wthread_init;
	int i, ret, fd, diff_sec, nok = 0;
	long soffset, foffset;
	char *fmt;

	if (req->proto == PROTO_HTTP) 
		http_head_req(req);
	
	/* According to the content-length, get the
	 * suggested number of threads to open.
	 * if the user insists on his value, let it be that way,
	 * use the user's value.
	 */
	ret = numofthreads(req->clength);

	if (fsuggested == 0) {
		if (ret == 0)
			nthreads = SINIT(1);
		else
			nthreads = SINIT(ret);
	}

	wthread_init = malloc(nthreads * sizeof(struct thread_data));

	Log("Downloading %s (%d bytes) from site %s(%s:%d). Number of Threads: %d",
			req->url, req->clength, req->host, req->ip, req->port, nthreads);

	if (strlen(req->lfile) != 0) {
		if ((fd = open(req->lfile, O_CREAT | O_RDWR, S_IRWXU)) == -1) {
			fprintf(stderr, "get: cannot open file %s for writing: %s\n", req->lfile, strerror(errno));
			exit(1);
		}
		
	} else {
		if ((fd = open(req->file, O_CREAT | O_RDWR, S_IRWXU)) == -1) {
			fprintf(stderr, "get: cannot open file %s for writing: %s\n", req->lfile, strerror(errno));
			exit(1);
		}
	}

	if ((lseek(fd, req->clength - 1, SEEK_SET)) == -1) {
		fprintf(stderr, "get: couldn't lseek:  %s\n", strerror(errno));
		exit(1);
	}

	if ((write(fd, NTDROP(NTEXPAND("0")), 1)) == -1) {
		fprintf(stderr, "get: couldn't allocate space for download file: %s\n", strerror(errno));
		exit(1);
	}

	/* Get the starting time, prepare GET format string, and start the threads */
	fmt = (char *)calloc(GETREQSIZ, sizeof(char));
	time(&t_start);
	for (i = 0; i < nthreads; i++) {
		soffset = calc_offset(req->clength, i, nthreads);
		foffset = calc_offset(req->clength, i + 1, nthreads);
		wthread_init[i].soffset = soffset;
		wthread_init[i].foffset = (i == nthreads - 1 ? req->clength : foffset);
		wthread_init[i].sin.sin_family = AF_INET;
		wthread_init[i].sin.sin_addr.s_addr = inet_addr(req->ip);
		wthread_init[i].sin.sin_port = htons(req->port);
		wthread_init[i].fd = dup(fd);
		wthread_init[i].clength = req->clength;
		snprintf(fmt, GETREQSIZ, GETREQ, req->url, req->host, PROGVERSION, soffset);
		strncpy(wthread_init[i].getstr, fmt, GETREQSIZ);
	}
	free(fmt);

	wthread_tmp = SCAST(wthread_init);
	wthread = SINIT(wthread_tmp);

	start_signal_thread();
	for (i = 0; i < nthreads; i++) {
		pthread_create(&(wthread[i].tid), NULL, http_get, (void SDYNAMIC*SAFE)TC(&wthread[i]));
	}


	/* Wait for all of the threads to finish... 
	 * 
	 * TODO: If a thread fails, restart that!
	 */
	for (i = 0; i < nthreads; i++) {
		pthread_join(wthread[i].tid, NULL);
		printf("get: (%p)->status = %d\n", &wthread[i], wthread[i].status);
		if (wthread[i].status == STAT_OK)
			nok++;
	}

	printf("get: nok = %d, nthreads = %d\n", nok, nthreads);
	if (nok == nthreads) 
		pthread_cancel(hthread);
	else
		pthread_join(hthread, NULL);

	/* Get the finish time, derive some stats	*/
	time(&t_finish);
       	if ((diff_sec = t_finish - t_start) == 0)
		diff_sec = 1;   /* Avoid division by zero       */

	Log("Download completed, job completed in %d seconds. (%d Kb/sec)",
			diff_sec, (req->clength / diff_sec) / 1024);
        Log("Shutting down...");
	close(fd);
}


void resume_get(struct hist_data *h)
{
	struct thread_data SDYNAMIC* wthread_tmp;
	int i, fd, diff_sec, nok = 0;
	char *fmt;

	nthreads = SINIT(h->nthreads);

	fmt = (char *)calloc(GETREQSIZ - 2, sizeof(char));

	wthread_tmp = malloc(nthreads * sizeof(struct thread_data));
	wthread = SINIT(wthread_tmp);

	memcpy(req, &h->req, sizeof(struct request));
	memcpy(wthread, h->wthread, sizeof(struct thread_data) * nthreads);

	Log("Resuming download %s (%d bytes) from site %s(%s:%d). Number of Threads: %d",
			req->url, req->clength, req->host, req->ip, req->port, nthreads);

	if (strlen(req->lfile) != 0) {
		if ((fd = open(req->lfile, O_RDWR, S_IRWXU)) == -1) {
			fprintf(stderr, "get: cannot open file %s for writing: %s\n", req->lfile, strerror(errno));
			exit(1);
		}
		
	} else {
		if ((fd = open(req->file, O_RDWR, S_IRWXU)) == -1) {
			fprintf(stderr, "get: cannot open file %s for writing: %s\n", req->lfile, strerror(errno));
			exit(1);
		}
	}

	time(&t_start);


#ifdef DEBUG
	for (i = 0; i < nthreads; i++)
		printf("Start: %ld, Finish: %ld, Offset: %ld, Diff: %ld\n",
				wthread[i].soffset,
				wthread[i].foffset,
				wthread[i].offset,
				wthread[i].offset - wthread[i].soffset);
#endif

	start_signal_thread();
	for (i = 0; i < nthreads; i++) {
		wthread[i].soffset = wthread[i].offset;
		wthread[i].fd = dup(fd);
		snprintf(fmt, GETREQSIZ, GETREQ, req->url, req->host, PROGVERSION, wthread[i].offset);
		strncpy(wthread[i].getstr, fmt, GETREQSIZ);
		pthread_create(&(wthread[i].tid), NULL, http_get, (void SDYNAMIC*SAFE)TC(&wthread[i]));
	}

	for (i = 0; i < nthreads; i++)
		pthread_join(wthread[i].tid, NULL);

	for (i = 0; i < nthreads; i++) {
		pthread_join(wthread[i].tid, NULL);
		if (wthread[i].status == STAT_OK)
			nok++;
	}

	if (nok == nthreads) 
		pthread_cancel(hthread);
	else
		pthread_join(hthread, NULL);



       time(&t_finish);
       if ((diff_sec = t_finish - t_start) == 0)
		diff_sec = 1;   /* Avoid division by zero       */

	Log("Download completed, job completed in %d seconds. (%d Kb/sec)",
			diff_sec, ((req->clength - h->bwritten) / diff_sec) / 1024);
        Log("Shutting down...");
	close(fd);
}
