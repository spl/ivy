static int printlog, shortlog;
static char *logfile;
static int slow_realloc, free_refed;

static void parse_options(void)
{
  char *opts = getenv("HEAPSAFE"), *token;

  /*  Special case SPEC runs to avoid polluting stderr */
  if (getenv("SPEC"))
    logfile = "/dev/tty";

  while ((token = strtok(opts, " ")))
    {
      opts = NULL;

      if (!strcmp(token, "log"))
	printlog = 1;
      else if (!strcmp(token, "shortlog"))
	printlog = shortlog = 1;
      else if (!strncmp(token, "logfile=", 8))
	logfile = token + 8;
      else if (!strcmp(token, "slow_realloc"))
	slow_realloc = 1;
      else if (!strcmp(token, "forcefree"))
	free_refed = 1;
    }
}
