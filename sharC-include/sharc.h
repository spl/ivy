#ifndef __SHARC_H_
#define __SHARC_H_

/**
 * qualifiers for function types
 */

#define SINTHREAD          __attribute__((sinthread))
#define SFNPTR             __attribute__((sfnptr))
#define SHASDEF            __attribute__((shasdef))
#define SPURE              __attribute__((spure))
#define STCREATE(fn,arg)   __attribute__((stcreate((fn),(arg))))

/**
 * qualifiers for any time
 */

#define SLOCKED(l)         __attribute__((slocked((l))))
#define SREADONLY          __attribute__((sreadonly))
#define SRACY              __attribute__((sracy))
#define SREADS(n)          __attribute__((sreads((n))))
#define SWRITES(n)         __attribute__((swrites((n))))
#define SREADSNT           __attribute__((sreadsnt))
#define SWRITESNT          __attribute__((swritesnt))
#define SCTX               __attribute__((sctx))
#define SPRIVATE           __attribute__((sprivate))
#define SDYNAMIC           __attribute__((sdynamic))
#define SINDYNAMIC         __attribute__((sindynamic))
#define SOUTDYNAMIC        __attribute__((soutdynamic))
#define SDYNBAR(b)         __attribute__((sdynbar((b))))

/* For structure instances that are members of a group
   where the group is identified by the value of g */
#define SGROUP(g)          __attribute__((sgroup((g))))

/* For pointer target types of structure fields.
   Indicates that target is member of same group as
   the structure, and is in the same mode */
#define SSAME              __attribute__((ssame))


#ifdef __SHARC__
/** Sharing cast */
void *SCAST(void *);

/** Readonly initialization */
void *SINIT(void *);
double SINIT_DOUBLE(double d);
float SINIT_FLOAT(float f);
#else
#define SCAST(x) ({__typeof(x) __tmp = (x); (x) = NULL; __tmp; })
#define SINIT(x) (x)
#define SINIT_DOUBLE(x) (x)
#define SINIT_FLOAT(x) (x)
#endif

#endif /* __SHARC_H_ */
