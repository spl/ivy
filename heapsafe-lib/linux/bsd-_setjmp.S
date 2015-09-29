/* setjmp for i386.
   Copyright (C) 1995, 1996, 1997, 2000, 2001 Free Software Foundation, Inc.
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

#define _ASM
#define _SETJMP_H
#include <bits/setjmp.h>

#ifndef	JB_BX
#define JB_BX   0
#define JB_SI   1
#define JB_DI   2
#define JB_BP   3
#define JB_SP   4
#define JB_PC   5
#endif
	
#define JMPBUF 4
#define VAL 8
	
	.globl _setjmp
	.type _setjmp,@function
	.align 1<<4
_setjmp:
	movl JMPBUF(%esp), %eax
     	/* Save registers.  */
	movl %ebx, (JB_BX*4)(%eax)
	movl %esi, (JB_SI*4)(%eax)
	movl %edi, (JB_DI*4)(%eax)
	leal JMPBUF(%esp), %ecx	/* Save SP as it will be after we return.  */
     	movl %ecx, (JB_SP*4)(%eax)
	movl 0(%esp), %ecx	/* Save PC we are returning to now.  */
     	movl %ecx, (JB_PC*4)(%eax)
	movl %ebp, (JB_BP*4)(%eax) /* Save caller's frame pointer.  */

	/* Make a tail call to __jmp_save; it takes the same args.  */
	jmp __jmp_save
	.size _setjmp,.-_setjmp

	.globl __sigsetjmp
	.type __sigsetjmp,@function
	.align 1<<4
__sigsetjmp:	
	movl JMPBUF(%esp), %eax
     	/* Save registers.  */
	movl %ebx, (JB_BX*4)(%eax)
	movl %esi, (JB_SI*4)(%eax)
	movl %edi, (JB_DI*4)(%eax)
	leal JMPBUF(%esp), %ecx	/* Save SP as it will be after we return.  */
     	movl %ecx, (JB_SP*4)(%eax)
	movl 0(%esp), %ecx	/* Save PC we are returning to now.  */
     	movl %ecx, (JB_PC*4)(%eax)
	movl %ebp, (JB_BP*4)(%eax) /* Save caller's frame pointer.  */

	/* Make a tail call to __jmp_save; it takes the same args.  */
	jmp __sigjmp_save
	.size __sigsetjmp,.-__sigsetjmp
	
	.globl __longjmp
	.type __longjmp,@function
	.align 1<<4
__longjmp:	
        movl JMPBUF(%esp), %ecx   /* User's jmp_buf in %ecx.  */
        movl VAL(%esp), %eax    /* Second argument is return value.  */
        /* Save the return address now.  */
        movl (JB_PC*4)(%ecx), %edx
        /* Restore registers.  */
        movl (JB_BX*4)(%ecx), %ebx
        movl (JB_SI*4)(%ecx), %esi
        movl (JB_DI*4)(%ecx), %edi
        movl (JB_BP*4)(%ecx), %ebp
        movl (JB_SP*4)(%ecx), %esp
        /* Jump to saved PC.  */
        jmp *%edx
	.size __longjmp,.-__longjmp
