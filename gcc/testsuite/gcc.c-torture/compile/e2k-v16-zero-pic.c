/* A loop storing zero vectors.  Under -fPIC the zero stays a constant
   (it can't go to the constant pool), and a 16-byte store on E2K v5
   and later must still take it from a register.  */
/* { dg-additional-options "-fPIC" { target fpic } } */
/* { dg-additional-options "-fno-tree-loop-distribute-patterns" } */
/* { dg-additional-options "-march=elbrus-v5" { target e2k*-*-* } } */

void
f (unsigned long *p, long n)
{
  for (long i = 0; i < n; i++)
    p[i] = 0;
}
