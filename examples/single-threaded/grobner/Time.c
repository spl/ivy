#include <sys/types.h>
#include <sys/time.h>

void itimerinit(int timerid, int setval)
{
	struct itimerval again;
	again.it_interval.tv_sec = setval;
	again.it_interval.tv_usec = 0;
	again.it_value.tv_sec = setval;
	again.it_value.tv_usec = 0;
	setitimer(timerid, &again, (struct itimerval*) 0);
	return;
}

float itimerread (int timerid)
{
	struct itimerval thistime;
	getitimer ( timerid, &thistime );
	return (float)thistime.it_value.tv_sec + 1e-6*(float)thistime.it_value.tv_usec;
}

