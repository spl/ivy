/* Copyright (C) 1991,92,94,95,97,98,2000,2002 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, write to the Free
   Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307 USA.  */

/* Changes made by David Gay (david.e.gay@intel.com) in Autumn 2007 to
   support HeapSafe's extended jmp_buf environment.
*/

#define __HEAPSAFE__
#define __HS_LIB__

#include <stddef.h>
#include "../../heapsafe-include/Linux/setjmp.h"
#include <signal.h>
#include <heapsafe.h>
#include <symbols.h>
#include <stdlib.h>

/* Internal machine-dependent function to restore context sans signal mask.  */
extern void __longjmp (__jmp_buf __env, int __val)
     __attribute__ ((__noreturn__));

static void deref_locals(void **istart, void **iend)
{
  /* Remove references due to local-variables-from-skipped-stack-frames
     which aren't handled by direct_vars (structs, arrays, variables
     whose address is taken) */
  for (; istart < iend; istart += 3)
    {
      void *obj = istart[0];
      size_t osize = (size_t)istart[1];
      hs_type_t oadj = (hs_type_t)istart[2];

      if (oadj)
#ifdef __HS_NOCONCRC__
        oadj(obj, -1, osize);
#else
        oadj(obj, 0, osize, 1);
#endif
    }
}

#ifndef __HS_NOCONCRC__
static void pop_direct_vars(int old_head)
{
    struct chs_thread *t = __this_chs_thread;

    while (t->dvar_head != old_head)
        __hs_builtin_cpop(t->direct_vars[t->dvar_head].addr);
}
#endif

/* Set the signal mask to the one specified in ENV, and jump
   to the position specified in ENV, causing the setjmp
   call there to return VAL, or 1 if VAL is 0.  */
void
__libc_siglongjmp (sigjmp_buf env, int val)
{
  if (env[0].__mask_was_saved)
    /* Restore the saved signal mask.  */
    (void) sigprocmask (SIG_SETMASK, &env[0].__saved_mask,
			  (sigset_t *) NULL);

#ifdef __HS_NOCONCRC__
  deref_locals(env[0].hs_indirect_vars, __hs_indirect_vars);

  /* Restore RC's local var info */
  __hs_indirect_vars = env[0].hs_indirect_vars;
  __hs_direct_vars = env[0].hs_direct_vars;
  if (__hs_scount)
    {
      __hs_scount = env[0].hs_scount + 1;
      hs_delayed_free_end();
    }
  else if (env[0].hs_scount)
    abort();
#else /* if __HS_CONCRC__ */
  deref_locals(env[0].hs_indirect_vars, __this_chs_thread->indirect_vars_pos);

  /* Restore RC's local var info */
  __this_chs_thread->indirect_vars_pos = env[0].hs_indirect_vars;
  pop_direct_vars(env[0].dvar_head);
  if (__this_chs_thread->__hs_scount)
    {
      __this_chs_thread->__hs_scount = env[0].hs_scount + 1;
      hs_delayed_free_end();
    }
  else if (env[0].hs_scount)
    abort();
#endif

  /* Call the machine-dependent function to restore machine state.  */
  __longjmp (env[0].__jmpbuf, val ?: 1);
}

strong_alias (__libc_siglongjmp, __libc_longjmp)
strong_alias (__libc_siglongjmp, _longjmp)
strong_alias (__libc_siglongjmp, longjmp)
strong_alias (__libc_siglongjmp, siglongjmp)
