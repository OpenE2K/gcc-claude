/* Global registers and asm, as MCST's kernel uses them (lcc reads asm
   templates): an asm whose template writes a global register it doesn't
   declare must not make a value copied from the register before it be
   read again from the register after (f); and a store to a fixed global
   register must survive an asm that names the register as a clobber
   (g, as the kernel's barrier() does).  */
/* { dg-skip-if "E2K asm" { ! e2k*-*-* } } */
/* { dg-additional-options "-ffixed-g20 -ffixed-g21" } */

struct s { long a[8]; };

register struct s *base __asm__ ("%g20");
register unsigned long flags __asm__ ("%g21");

static struct s one = { { 1, 2, 3, 4, 5, 6, 7, 8 } };
static struct s two = { { 10, 20, 30, 40, 50, 60, 70, 80 } };

__attribute__((noinline)) long
f (struct s *next)
{
  struct s *t = base;
  __asm__ __volatile__ ("addd %0, 0x0, %%dg20" : : "r" (next));
  return t->a[3] + t->a[5];
}

__attribute__((noinline)) void
g (void)
{
  int unused;
  flags |= 4;
  __asm__ ("" : "=r" (unused) : : "memory", "g21");
}

int
main (void)
{
  base = &one;
  if (f (&two) != 4 + 6)
    __builtin_abort ();
  flags = 1;
  g ();
  if (flags != 5)
    __builtin_abort ();
  return 0;
}
