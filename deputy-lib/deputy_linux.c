#include <linux/config.h>    /* has to be first!  */
#include <linux/init.h>
#include <linux/module.h>
#ifdef CONFIG_KRECOVER
#include <linux/krecover.h>
#endif

#define IN_DEPUTY_LIBRARY

#include "deputy/checks.h"

asmlinkage
void deputy_fail_mayreturn(const char *check, const char *text,
                           __LOCATION__FORMALS) {
    printk(KERN_ALERT
           "%s:%d: %s: Assertion failed in %s: %s\n", 
           __LOCATION__ACTUALS, check, text);
    dump_stack();
#ifdef CONFIG_KRECOVER
    /* This will trigger real krecover recovery */
    if (kr_recovery_enabled)
        kr_trigger_fault();
#endif
}

asmlinkage noreturn
void deputy_fail_noreturn_fast(void) {
    panic("Deputy assertion failure\n");
}

int deputy_strlen(const char *str) {
    return strlen(str);
}

char *deputy_strcpy(char *dest, const char *src) {
    char *tmp = dest;
    while ((*dest++ = *src++) != '\0') {
        // do nothing
    }
    return tmp;
}

char *deputy_strncpy(char *dest, const char *src, size_t count) {
    char *tmp = dest;
    int c = count;
    while (c >= 0) {
        if ((*tmp = *src) != 0) src++;
        tmp++;
        c--;
    }
    return dest;
}

/* Search for a NULL starting at e and return its index */
int deputy_findnull(const void *e, unsigned int bytes) {
#define NULLCHECK(type) \
    do { \
        type *p = (type*) e; \
        while (*p != 0) { \
            p++; \
        } \
        length = (p - (type*) e); \
    } while (0)

    int length = 0;

    switch (bytes) {
        case 1:
            NULLCHECK(char);
            break;
        case 2:
            NULLCHECK(short);
            break;
        case 4:
            NULLCHECK(long);
            break;
        default:      
            printk(KERN_ALERT "Invalid byte size for nullcheck.\n");
            break;
    }

    return length;
#undef NULLCHECK
}

void *__deputy_memset(void *s, int c, unsigned int n) {
  return memset(s, c, n);
}
