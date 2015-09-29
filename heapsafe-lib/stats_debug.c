static unsigned long alloc_count, free_count, scoped_count;
static unsigned long alloc_current_bytes, alloc_max_bytes;
static unsigned long alloc_actual_current_bytes, alloc_actual_max_bytes;
static unsigned long long alloc_bytes, alloc_actual_bytes;

static size_t realsize(size_t s)
{
  size_t n = (s < sizeof(mchunk) - CHUNK_OVERHEAD - 1) ?
    16 : (s + CHUNK_OVERHEAD + 7) & ~7;

  if (n >= mparams.mmap_threshold)
    n = granularity_align(n + SIX_SIZE_T_SIZES + 7);

  n += n >> 3; /* Ref counts */

  return n;
}

static void stats_allocating(size_t n)
{
  alloc_count++;

  alloc_bytes += n;
  alloc_current_bytes += n;
  if (alloc_current_bytes > alloc_max_bytes)
    alloc_max_bytes = alloc_current_bytes;

  alloc_actual_bytes += realsize(n);
  alloc_actual_current_bytes += realsize(n);
  if (alloc_actual_current_bytes > alloc_actual_max_bytes)
    alloc_actual_max_bytes = alloc_actual_current_bytes;
}

static void stats_freeing(size_t n)
{
  free_count++;
  alloc_current_bytes -= n;
  alloc_actual_current_bytes -= realsize(n);
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
      mprintf(", %10lu, %10lu, %10lu", alloc_count, free_count, scoped_count);
      mprintf(", %16llu, %16llu", alloc_bytes, alloc_actual_bytes);
      mprintf(", %10lu, %10lu\n", alloc_max_bytes, alloc_actual_max_bytes);
    }
  else
    {
      mprintf("%lu allocations, %lu frees (%lu scoped)\n",
	      alloc_count, free_count, scoped_count);
      mprintf("%llu requested bytes, %llu actual bytes\n",
	      alloc_bytes, alloc_actual_bytes);
      mprintf("max memory use: %lu\n", alloc_max_bytes);
      mprintf("max actual memory use: %lu\n", alloc_actual_max_bytes);
    }
}
