// { dg-do run }
// A call's result stored into a base subobject whose tail padding the
// derived class reuses: store_field stores it as a bit-field.  On E2K
// the 24-byte result comes back in registers, a PARALLEL wider than
// any integer mode.

struct B
{
  B (int);
  long a, b;
  int c;
};

B::B (int x) : a (x), b (x + 1), c (x + 2) {}

__attribute__ ((noipa)) B
make (int x)
{
  return B (x);
}

struct D : B
{
  int d;
  D (int x) : B (make (x)), d (x + 3) {}
};

int
main ()
{
  D v (1);
  if (v.a != 1 || v.b != 2 || v.c != 3 || v.d != 4)
    __builtin_abort ();
  return 0;
}
