static unsigned long alloc_count, free_count, scoped_count;
static unsigned long alloc_actual_current_bytes, alloc_actual_max_bytes;
static unsigned long long alloc_actual_bytes;

static void stats_allocating(size_t n)
{
  alloc_count++;

#ifdef __HS_LIB__
  n = n + (n >> __HS_RCLOG);
#endif
  alloc_actual_bytes += n;
  alloc_actual_current_bytes += n;
  if (alloc_actual_current_bytes > alloc_actual_max_bytes)
    alloc_actual_max_bytes = alloc_actual_current_bytes;
}

static void stats_freeing(size_t n)
{
#ifdef __HS_LIB__
  n = n + (n >> __HS_RCLOG);
#endif
  free_count++;
  alloc_actual_current_bytes -= n;
}

static void stats_scope(size_t scope_n)
{
  scoped_count += scope_n;
  scope_n *= 8;
  if (alloc_actual_current_bytes + scope_n > alloc_actual_max_bytes)
    alloc_actual_max_bytes = alloc_actual_current_bytes + scope_n;
}

static void stats_report(int shortlog)
{
  if (shortlog)
    {
      mprintf(", %10lu, %10lu, %lu", alloc_count, free_count, scoped_count);
      mprintf(", %16llu, %16llu", 0, alloc_actual_bytes);
      mprintf(", %10lu, %10lu\n", 0, alloc_actual_max_bytes);
    }
  else
    {
      mprintf("%lu allocations, %lu frees (%lu scoped)\n",
	      alloc_count, free_count, scoped_count);
      mprintf("%llu actual bytes\n", alloc_actual_bytes);
      mprintf("max actual memory use: %lu\n", alloc_actual_max_bytes);
    }
}
