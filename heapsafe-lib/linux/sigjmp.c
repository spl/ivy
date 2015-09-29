/* Copyright (C) 1992, 1994, 1997 Free Software Foundation, Inc.
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
#include <stdlib.h>
#include <heapsafe.h>

/* This function is called by the `sigsetjmp' macro
   before doing a `__setjmp' on ENV[0].__jmpbuf.
   Always return zero.  */

int
__sigjmp_save (sigjmp_buf env, int savemask)
{
  env[0].__mask_was_saved = (savemask &&
			     sigprocmask (SIG_BLOCK, (sigset_t *) NULL,
					    &env[0].__saved_mask) == 0);

#ifdef __HS_NOCONCRC__
  env[0].hs_direct_vars = __hs_direct_vars;
  env[0].hs_indirect_vars = __hs_indirect_vars;
  env[0].hs_scount = __hs_scount;
#else
  //env[0].hs_direct_vars = __this_chs_thread->direct_vars_pos;
  env[0].dvar_head = __this_chs_thread->dvar_head;
  env[0].hs_indirect_vars = __this_chs_thread->indirect_vars_pos;
  env[0].hs_scount = __this_chs_thread->__hs_scount;
#endif

  return 0;
}

int
__jmp_save (sigjmp_buf env)
{
  env[0].__mask_was_saved = 0;

#ifdef __HS_NOCONCRC__
  env[0].hs_direct_vars = __hs_direct_vars;
  env[0].hs_indirect_vars = __hs_indirect_vars;
  env[0].hs_scount = __hs_scount;
#else
  //env[0].hs_direct_vars = __this_chs_thread->direct_vars_pos;
  env[0].dvar_head = __this_chs_thread->dvar_head;
  env[0].hs_indirect_vars = __this_chs_thread->indirect_vars_pos;
  env[0].hs_scount = __this_chs_thread->__hs_scount;
#endif

  return 0;
}

