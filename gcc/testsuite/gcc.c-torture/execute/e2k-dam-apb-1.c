/* A histogram whose keys repeat often, so that a pipelined loop's lock
   loads fail their checks and its compensation code runs while array
   prefetch reads the keys (E2K).  */

#define N (1 << 16)
#define M 64

int keys[N], out[N], h[M], ref[M];

__attribute__((noinline)) void
hist (int n)
{
  for (int i = 0; i < n; i++)
    {
      out[i] = keys[i];
      h[keys[i]]++;
    }
}

int
main (void)
{
  unsigned s = 12345;
  for (int i = 0; i < N; i++)
    {
      s = s * 1103515245u + 12345u;
      /* Runs of near repeats.  */
      keys[i] = (i & 8) ? (s >> 16) % 3 : (s >> 16) % M;
      ref[keys[i]]++;
    }
  for (int r = 0; r < 3; r++)
    {
      for (int j = 0; j < M; j++)
	h[j] = 0;
      hist (N);
      for (int j = 0; j < M; j++)
	if (h[j] != ref[j])
	  __builtin_abort ();
      for (int i = 0; i < N; i++)
	if (out[i] != keys[i])
	  __builtin_abort ();
    }
  return 0;
}
