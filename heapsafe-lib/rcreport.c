enum logkind {
  REPORT_RCOP,
  REPORT_RCADJOP,
  REPORT_RCLOCALOP,
  REPORT_RCILOCALOP,
  REPORT_ALLOC,
  REPORT_ALLOC_SIZE,
  REPORT_ALLOC_NOCLEAR,
  REPORT_POSFREE,
  REPORT_NEGFREE,
  REPORT_NOTYPE,
  REPORT_GPOSFREE,
  REPORT_GNEGFREE,
  REPORT_GNOTYPE,
  REPORT_LEAK,
  REPORT_GLEAK,
  REPORT_SCOPESIZE,
  REPORT_SCOPECOUNT
};

static char *repkinds[] = {
  "refcount                ",
  "refcount adjust         ",
  "local push              ",
  "indirect local push     ",
  "allocated               ",
  "allocated bytes         ",
  "allocated (noclear)     ",
  "referenced              ",
  "negative refcount (BUG) ",
  "type information missing",
  "referenced (g)          ",
  "negative rc (g, BUG)    ",
  "type info missing (g)   ",
  "leak                    ",
  "leak (g)                ",
  "scopesize               ",
  "scopecount              "
};

enum countmode {
   MODE_COUNT,
   MODE_SUM,
   MODE_MAX
};

enum countmode logkind_mode(enum logkind kind){
   switch (kind){
      case REPORT_SCOPESIZE: case REPORT_SCOPECOUNT:
          return MODE_MAX;
      case REPORT_ALLOC_SIZE:
          return MODE_SUM;
      default:
          return MODE_COUNT;        
   }
}

#include "dhash.h"
#include "dhash.c"

static dhash_table memproblems;

struct memreport
{
  int kind;
  const char *s1;
  int n1;
  const char *s2;
  int n2;
  unsigned long count;
};

static unsigned long rephash(void *key)
{
  struct memreport *rep = key;

  return (rep->n1 * rep->n2) ^ rep->kind ^
    *(unsigned long *)rep->s1 ^ (rep->s2 ? *(unsigned long *)rep->s2 : 111);
}

static bool repcompare(void *px, void *py)
{
  struct memreport *x = px, *y = py;

  return x->n1 == y->n1 && x->n2 == y->n2 && x->kind == y->kind &&
    !strcmp(x->s1, y->s1) &&
    (x->s2 && y->s2 ? !strcmp(x->s2, y->s2) : x->s2 == y->s2);
}

static void prt_memreport(void)
{
  if (!memproblems)
    return;

  dhash_scan scan = dhscan(memproblems);
  struct memreport *report;

  while ((report = dhnext(&scan)))
    if (report->s2)
      mprintf("%s %10lu times. Allocated at %s:%d, %s %s:%d\n",
	      repkinds[report->kind], report->count,
	      report->s1, report->n1,
	      report->kind != REPORT_GLEAK ? "freed at" : "in group",
	      report->s2, report->n2);
    else
      mprintf("%s %10lu times. Allocated at %s:%d\n",
	      repkinds[report->kind], report->count,
	      report->s1, report->n1);
}

void memreport_full(int kind, const char *s1, int n1, const char *s2, int n2, int count)
{
  struct memreport *report, key;

  if (!memproblems)
    memproblems = new_dhash_table(256, repcompare, rephash);
  key.kind = kind;
  key.s1 = s1; key.n1 = n1; key.s2 = s2; key.n2 = n2;
  report = dhlookup(memproblems, &key);
  if (!report)
    {
      report = dlmalloc(sizeof *report);
      *report = key;
      report->count = 0;
      dhadd(memproblems, report);
    }
    
  switch (logkind_mode(kind)){
    case MODE_COUNT:
      report->count++; return;
    case MODE_SUM:
      assert(count != 0);
      report->count += count; return;
    case MODE_MAX:
      if(report->count < count){
         report->count = count;
      }
      return;
  }  
}

void memreport(int kind, const char *s1, int n1, const char *s2, int n2)
{
  memreport_full(kind,s1,n1,s2,n2,0);
}
