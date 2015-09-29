/* Copyright (c) 2007 Intel Corporation 
 * All rights reserved. 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 	Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 	Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *     Neither the name of the Intel Corporation nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE INTEL OR ITS
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#define __HEAPSAFE__
#define __HS_LIB__

#include "../../heapsafe-include/Darwin/setjmp.h"
#include <heapsafe.h>
#include <stdlib.h>

#define JB_DVARS 18
#define JB_IVARS 19
#define JB_SCOUNT 20

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
  struct chs_thread *t = GET_CHS_THREAD();

  while (t->dvar_head != old_head)
    __hs_builtin_cpop(t->direct_vars[t->dvar_head].addr);
}
#endif

static void hs_restore(jmp_buf env)
{
#ifdef __HS_NOCONCRC__
  deref_locals((void **)env[JB_IVARS], __hs_indirect_vars);

  /* Restore RC's local var info */
  __hs_indirect_vars = (void **)env[JB_IVARS];
  __hs_direct_vars = (void **)env[JB_DVARS];
  if (__hs_scount)
    {
      __hs_scount = env[JB_SCOUNT] + 1;
      hs_delayed_free_end();
    }
  else if (env[JB_SCOUNT])
    abort();
#else
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  deref_locals((void **)env[JB_IVARS], this_chs_thread->indirect_vars_pos);

  /* Restore RC's local var info */
  this_chs_thread->indirect_vars_pos = (void **)env[JB_IVARS];
  //this_chs_thread->direct_vars_pos = (void **)env[JB_DVARS];
  pop_direct_vars(env[JB_DVARS]);
  if (this_chs_thread->__hs_scount)
    {
      this_chs_thread->__hs_scount = env[JB_SCOUNT] + 1;
      hs_delayed_free_end();
    }
  else if (env[JB_SCOUNT])
    abort();
#endif
}

static void hs_save(jmp_buf env)
{
#ifdef __HS_NOCONCRC__
  env[JB_DVARS] = (int)__hs_direct_vars;
  env[JB_IVARS] = (int)__hs_indirect_vars;
  env[JB_SCOUNT] = __hs_scount;
#else
  struct chs_thread *this_chs_thread = GET_CHS_THREAD();
  env[JB_DVARS] = (int)this_chs_thread->dvar_head;
  env[JB_IVARS] = (int)this_chs_thread->indirect_vars_pos;
  env[JB_SCOUNT] = this_chs_thread->__hs_scount;
#endif
}

int __hs_setjmp(jmp_buf env);
void __hs_longjmp(jmp_buf env, int val);
int __hs__setjmp(jmp_buf env);
void __hs__longjmp(jmp_buf, int val);

int setjmp(jmp_buf env)
{
  hs_save(env);
  return __hs_setjmp(env);
}

void longjmp(jmp_buf env, int val)
{
  hs_restore(env);
  __hs_longjmp(env, val);
}

int _setjmp(jmp_buf env)
{
  hs_save(env);
  return __hs__setjmp(env);
}

void _longjmp(jmp_buf env, int val)
{
  hs_restore(env);
  __hs__longjmp(env, val);
}
