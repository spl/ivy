#include <stdio.h>
#include "cmump.h"
#include "multpol.h"

extern char *varnames[];


void mpolout (MPOL *p)
{
	int	i, j;

	if (p -> nterms == 0)
		printf ("0");
	else {
		for (i = 0; i < p -> nterms; i++) {
			if (mtest (&(p -> coefs[i])) < 0) {
			  if ((meqshort(&(p->coefs[i]),-1))&&(!expozero(MEXPO(p,i), p->nvp1 - 1)))
					printf ("- ");
				else {
					mout (&(p -> coefs[i]));
					printf (" ");
				}
			}
			else {
				if (i != 0)
					printf ("+ ");
				if (!meqshort(&(p -> coefs[i]), 1) || expozero(MEXPO(p,i), p->nvp1 - 1)){
					mout (&(p -> coefs[i]));
					printf (" ");
				}
			}
			for (j = 0; j < p->nvp1 - 1; j++)
				switch (*(MPOW (p, i, j))) {
				case 0: 
					break;
				case 1: 
					printf ("%s ", varnames[j]);
					break;
				default: 
					printf ("%s^%d ", varnames[j], *(MPOW (p, i, j)));
					break;
				}
			printf (" ");
		}
	}
}




void Smpolout (char *s, MPOL *p)
{
	int	    i,
	j;

	if (p -> nterms == 0)
		sprintf (s + strlen (s), "0");
	else {
		for (i = 0; i < p -> nterms; i++) {
			if (mtest (&(p -> coefs[i])) < 0) {
			  if ((meqshort(&(p -> coefs[i]),-1)) && (!expozero(MEXPO(p,i), p->nvp1 - 1)))
					sprintf (s + strlen (s), "- ");
				else {
					Smout (s + strlen (s), &(p -> coefs[i]));
					sprintf (s + strlen (s), " ");
				}
			}
			else {
				if (i != 0)
					sprintf (s + strlen (s), "+ ");
				if (!meqshort (&(p->coefs[i]),1) || expozero(MEXPO(p,i), p->nvp1 - 1)) {
					Smout (s + strlen (s), &(p -> coefs[i]));
					sprintf (s + strlen (s), " ");
				}
			}
			for (j = 0; j < p->nvp1 - 1; j++)
				switch (*(MPOW (p, i, j))) {
				case 0: 
					break;
				case 1: 
					sprintf (s+strlen (s), "%s ", varnames[j]);
					break;
				default: 
					sprintf (s+strlen (s),"%s^%d ",varnames[j],*(MPOW(p,i,j)));
					break;
				}
			sprintf (s + strlen (s), " ");
		}
	}
}

