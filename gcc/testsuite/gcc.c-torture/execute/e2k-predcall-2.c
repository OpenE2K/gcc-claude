/* A call after an arm that ends in a noreturn call.  If the arm runs
   under a predicate, its prepare of the noreturn callee must not
   replace the callee the call after it reads (the two calls of f are
   prepared once, before the test).  */

int seen;

__attribute__((noinline)) void f (int x) { seen += x; }
__attribute__((noinline, noreturn)) void g (void) { __builtin_abort (); }

__attribute__((noinline)) void
t (void *data, void *expect)
{
  if (data != expect)
    {
      f (1);
      g ();
    }
  f (2);
}

int
main (void)
{
  int x;
  t (&x, &x);
  if (seen != 2)
    __builtin_abort ();
  return 0;
}
