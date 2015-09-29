//Use this file with "ccured --listnonsafe" to hide Deputy's annotations
//from CCured.
// "ANNOTATED" means that "ccured --listnonsafe" should suppress the warning,
// since this code is already Deputy-ready.

#ifdef CCURED
# define ANNOTATED __attribute__((annotated))
# define BND(b,e) ANNOTATED
# define COUNT(c) ANNOTATED __COUNT(c)
# define SIZE(c)  ANNOTATED
# define SAFE     ANNOTATED __SAFE
# define SNT      ANNOTATED
# define NT       ANNOTATED
# define NTS      ANNOTATED
# define NULLTERM ANNOTATED
# define POLY     ANNOTATED
# define TRUSTED  ANNOTATED
# define TC(x) __trusted_cast(x)
# define WHEN(c)  ANNOTATED

# define DMEMSET(x,y,z)
# define DMEMCPY(x,y,z)
# define DMEMCMP(x,y,z)
# define DALLOC(x)
#endif //ndef DEPUTY

