
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <pthread.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>

#include <sharc/sharc.h>

#include "Signal.h"
#include "Data.h"
#include "Resume.h"
#include "Misc.h"

extern pthread_t hthread;
extern int SREADONLY ASSUMECONST nthreads;
extern struct thread_data SDYNAMIC * COUNT(nthreads) SREADONLY wthread;
extern struct request *SAFE req;
extern unsigned int SLOCKED(&bwritten_mutex) bwritten;
extern pthread_mutex_t SRACY bwritten_mutex;

void * signal_waiter(void *arg)
{
	int signal;

	arg = NULL;

	pthread_sigmask(SIG_UNBLOCK, signal_set, NULL);
	
	while(1) {
		#ifdef SOLARIS
		sigwait(signal_set);
		#else
		sigwait(signal_set, &signal);
		#endif
		switch(signal) {
			case SIGINT:
				sigint_handler();
				break;
			case SIGALRM:
				sigalrm_handler();
				break;
		}
	}
}

void sigint_handler(void)
{
	int i;

	printf("^C caught, saving download job...\n");

	for (i = 0; i < nthreads; i++) {
		pthread_cancel(wthread[i].tid);
		wthread[i].status &= STAT_INT;		/* Interrupted download	*/
	}

	save_log();

	exit(0);
}


void sigalrm_handler(void)
{
	int bw;
	printf("Signal Alarm came\n");
	pthread_mutex_lock(&bwritten_mutex);
	bw = bwritten;
	pthread_mutex_unlock(&bwritten_mutex);
	updateProgressBar(bw, req->clength);
	alarm(1);
}

void start_signal_thread(void)
{
	/* Create a thread for hadling signals	*/
	if (pthread_create(&hthread, NULL, signal_waiter, NULL) != 0) {
		fprintf(stderr, "main: cannot create signal_waiter thread: %s, exiting...\n", strerror(errno));
		exit(-1);
	}

}
