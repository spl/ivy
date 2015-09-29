#include <stdio.h>
#include "cmump.h"

void mpfatal(char *s)
{
	printf("%s\n",s);
	(void) fflush(stdout);
	exit(0);
}

/* HISTORY
 *
 * 23-Apr-87  Bennet Yee (byee) at Carnegie-Mellon University
 *	Moved from Mutil so user can supply own fatal routine.
 * 18-May-84  Lyle McGeoch (magoo) at Carnegie-Mellon University
 *	Created from code in existing mp package. *
 *	Debugged, cleaned up, and sped up. *
 *	
 *	comment from soumen: this is the only function that is
 *	reasonably debugged. speed depends on the compiler.
 *
 */
