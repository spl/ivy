#ifndef __HS_LIB_H
#define __HS_LIB_H

/* =========================================================================
 * Redefine standard malloc/free operations in terms of malloc/free,
 * and memset/memcpy/memmove in terms of type-safe versions
 * You can include this with the -include to get an automatic start on porting
 * code to RC, or to keep code closer to the standard C APIs.
 *
 * Designed to be used with user-mode unix programs that use the standard
 * library. 
 * ========================================================================= */

/* include these ourselves so they aren't included again */
#include <stdlib.h>
#include <string.h>

#include <heapsafe.h>

#ifdef __HEAPSAFE__
#define malloc hs_malloc
#define memalign hs_memalign
#define calloc hs_calloc
#define realloc HS_REALLOC
#define free HS_FREE
#define memset HS_MEMSET
#define memcpy HS_MEMCPY
#define memmove HS_MEMMOVE
#endif

#endif /* __HS_LIB_H */
