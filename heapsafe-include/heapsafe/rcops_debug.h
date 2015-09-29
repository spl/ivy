#define __HS_RCLOG 5

typedef struct {
  const char *file;
  int line;
} __rc_location;

typedef struct __rcinfo {
  void *from;
  __rc_location loc;
  struct __rcinfo *next;
} __rcinfo;

extern __rc_location __rc_loc;

int __hs_rcref(void *from, void *ptr);
int __hs_rcderef(void *from, void *ptr);

#define RC_ADJUST(p, by) \
  ((p) ? ((by) > 0 ? __hs_rcref(&(p), (p)) : __hs_rcderef(&(p), (p))) : 0)

#ifndef __HEAPSAFE__
/* Strangely enough, this means the time we're included after the cil pass */

#define __builtin_hs_trace() (__rc_loc.file = __FILE__, __rc_loc.line = __LINE__)
#define __builtin_hs_adjust(adj, x, by, s) \
  (__builtin_hs_trace(), (adj)((x), (by), (s)))


#endif /* !__HEAPSAFE__ */
