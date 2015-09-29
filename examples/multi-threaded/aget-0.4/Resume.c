
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>

#include <sharc/sharc.h>

#include "Data.h"
#include "Resume.h"
#include "Misc.h"

extern int SREADONLY ASSUMECONST nthreads;
extern struct thread_data SDYNAMIC * COUNT(nthreads) SREADONLY wthread;
extern struct request *SAFE req;
extern pthread_mutex_t SRACY bwritten_mutex;
extern unsigned int SLOCKED(&bwritten_mutex) bwritten;


void save_log()
{
	char *logfile;
	struct hist_data h;
	FILE *fp;

	logfile = (char *)calloc(255, sizeof(char));


	if (strlen(req[0].lfile) == 0)
		snprintf(logfile, 255, "aget-%s.log", req[0].file);
	else
		snprintf(logfile, 255, "aget-%s.log", req[0].lfile);

	if ((fp = fopen(logfile, "w")) == NULL) {
		fprintf(stderr, "cannot open log file %s for writing: %s\n", logfile, strerror(errno));
		exit(1);
	}

	
	memcpy(&(h.req), req, sizeof(struct request));
	memcpy(&(h.wthread), wthread, sizeof(struct thread_data) * nthreads);
	h.nthreads = nthreads;
	pthread_mutex_lock(&bwritten_mutex);
	h.bwritten = bwritten;
	pthread_mutex_unlock(&bwritten_mutex);
	
	printf("--> Logfile is: %s, so far %d bytes have been transferred\n", logfile, h.bwritten);

	fwrite(TC(&h), sizeof(struct hist_data), 1, fp);
	fclose(fp);

	free(logfile);
}


int read_log(struct hist_data *SAFE h)
{
	char *logfile;
	FILE *fp;

	logfile = (char *)calloc(255, sizeof(char));


	if (strlen(req[0].lfile) == 0)
		snprintf(logfile, 255, "aget-%s.log", req[0].file);
	else
		snprintf(logfile, 255, "aget-%s.log", req[0].lfile);

	Log("Attempting to read log file %s for resuming download job...", logfile);

	if ((fp = fopen(logfile, "r")) == NULL) {
		if (errno == ENOENT) {
			Log("Couldn't find log file for this download, starting a clean job...");
			return -1;
		} else {
			fprintf(stderr, "cannot open log file %s for reading: %s\n", logfile, strerror(errno));
			exit(1);
		}
	}

	fread(TC(h), sizeof(struct hist_data), 1, fp);
	bwritten = h->bwritten;
	fclose(fp);

	Log("%d bytes already transferred", bwritten);

	/* Unlinking logfile after we've read it	*/
	if ((unlink(logfile)) == -1) 
		fprintf(stderr, "read_log: cannot remove stale log file %s: %s\n", logfile, strerror(errno));
		
	free(logfile);

	return 0;
}
