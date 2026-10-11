/* Calls in both arms of a branch: if-conversion may put each under a
   predicate, but each arm must still call its own function.  */

int seen;

__attribute__((noinline)) int f1 (int x) { seen += 1; return x + 1; }
__attribute__((noinline)) int f2 (int x) { seen += 100; return x * 2; }
__attribute__((noinline)) void v1 (void) { seen += 10; }
__attribute__((noinline)) void v2 (void) { seen += 1000; }

__attribute__((noinline)) int
g (int c, int x)
{
  int r;
  if (c)
    r = f1 (x);
  else
    r = f2 (x);
  return r;
}

__attribute__((noinline)) void
h (int c, int *p)
{
  if (c == 2)
    *p = f1 (*p);
  else
    *p = f2 (*p);
}

__attribute__((noinline)) void
k (int c)
{
  if (c > 0)
    v1 ();
  else
    v2 ();
}

int
main (void)
{
  if (g (1, 5) != 6 || g (0, 5) != 10)
    __builtin_abort ();
  int v = 3;
  h (2, &v);
  if (v != 4)
    __builtin_abort ();
  h (1, &v);
  if (v != 8)
    __builtin_abort ();
  k (1);
  k (0);
  if (seen != 1 + 100 + 1 + 100 + 10 + 1000)
    __builtin_abort ();
  return 0;
}
