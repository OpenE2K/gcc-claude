/* Copyright (C) 2009-2025 AO MCST. */

/* mcstbug #149583 */

#define MASK ((1 << 6 /* daz */) | (1 << 15 /* fz */))

static void __attribute__((constructor))
set_fast_math (void)
{
  unsigned int pfpfr;

  __asm__ ("rrs %%pfpfr, %0"
           : "=r" (pfpfr));

  pfpfr |= MASK;

  __asm__ ("rws %0, %%pfpfr"
           : : "r" (pfpfr));
}
