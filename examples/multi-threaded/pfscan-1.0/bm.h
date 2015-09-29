#ifndef PNSCAN_BM_H
#define PNSCAN_BM_H

#define BM_ASIZE 256 /* Allowed character code values */

typedef struct
{
    int *COUNT(saved_m) bmGs;
    int bmBc[BM_ASIZE];
    unsigned char *COUNT(saved_m) saved_x;
    int saved_m;
    int icase;
} BM;


extern int
bm_init(BM *bmp,
	unsigned char *COUNT(m) x,
	int m,
	int icase);

extern int
bm_search(BM *bmp,
	  unsigned char *COUNT(n) NT y,
	  size_t n,
	  int (*mfun)(unsigned char *COUNT(n) NT buf, size_t n, size_t pos, void *misc),
	  void *misc);

extern void
bm_destroy(BM *bmp);

#endif
