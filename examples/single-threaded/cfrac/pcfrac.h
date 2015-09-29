#ifndef PCFRAC_H
#define PCFRAC_H

typedef struct {
  unsigned *COUNT(len) primes;
  unsigned len;
} pfactors;		   

pfactors pfactorbase(precision n, unsigned k, unsigned m, unsigned aborts);
double  pomeranceLpow(double n, double alpha);

#endif
