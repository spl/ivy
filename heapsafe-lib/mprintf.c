#include <fcntl.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <unistd.h>

static int memerr = 2;

static void mprintf_init(void)
{
  if (logfile) {
    memerr = open(logfile, O_WRONLY | O_CREAT  | O_TRUNC, 0777);
  }
  if (memerr < 0)
    memerr = 2;
}

static void mprintf(const char *fmt, ...)
{
  va_list args;
  char buf[4096];
  int n;

  va_start(args, fmt);
  n = vsnprintf(buf, sizeof buf, fmt, args);
  va_end(args);

  if (n > 0)
    write(memerr, buf, n);
}

static void print_header(void)
{
  int cmdlinefd, cmdlinevalid = 0;
  char buf[4096];

  cmdlinefd = open("/proc/self/cmdline", O_RDONLY);
  if (cmdlinefd >= 0)
    {
      int n = read(cmdlinefd, buf, (sizeof buf) - 1), i;

      if (n >= 0)
	{
	  for (i = 0; i < n; i++)
	    if (!buf[i])
	      buf[i] = ' ';
	  buf[n] = '\0';
	  cmdlinevalid = 1;
	}
      close(cmdlinefd);
    }
  if (!cmdlinevalid)
    strcpy(buf, "unknown");

  if (shortlog)
    {
      char *lastslash = buf, *s = buf;
      char tmp[32];

      while (*s != ' ' && *s)
	if (*s++ == '/')
	  lastslash = s;

      strncpy(tmp, lastslash, 31);
      tmp[31] = 0;
      mprintf("\"%s\"%*s", tmp, 32 - strlen(tmp), " ");
    }
  else
    {
      mprintf("\nLog for %s\n", buf);
      mprintf("------------------------------------------------------------------\n");
    }
}
