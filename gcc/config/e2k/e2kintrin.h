/* lcc-compatible E2K intrinsics: the names lcc's <e2kintrin.h> defines.
   Written by Claude (Anthropic) as an experiment; see README.claude.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify it under
   the terms of the GNU General Public License as published by the Free
   Software Foundation; either version 3, or (at your option) any later
   version.

   GCC is distributed in the hope that it will be useful, but WITHOUT ANY
   WARRANTY; without even the implied warranty of MERCHANTABILITY or
   FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
   for more details.

   Under Section 7 of GPL version 3, you are granted additional
   permissions described in the GCC Runtime Library Exception, version
   3.1, as published by the Free Software Foundation.

   You should have received a copy of the GNU General Public License and
   a copy of the GCC Runtime Library Exception along with this program;
   see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
   <http://www.gnu.org/licenses/>.  */

/* Written from what the relcc2 specification measured of lcc's header
   (spec/abi/lcc-builtins.md, "<e2kintrin.h> helpers"; the names, their
   parameters and the constants' values from lcc-builtins-names.yaml),
   not from lcc's header, whose text is not free.  The compiler builtins
   need no header; this one adds the short forms _e2k_<op>, the vector
   types, the helper macros and the constants.  */

#ifndef _E2KINTRIN_H
#define _E2KINTRIN_H

#define __E2K_INLINE static __inline__ __attribute__ ((__always_inline__))

/* x86-style vector types: 16 bytes, then 8.  */
typedef long long __v2di __attribute__ ((__vector_size__ (16)));
typedef unsigned long long __v2du __attribute__ ((__vector_size__ (16)));
typedef double __v2df __attribute__ ((__vector_size__ (16)));
typedef int __v4si __attribute__ ((__vector_size__ (16)));
typedef unsigned int __v4su __attribute__ ((__vector_size__ (16)));
typedef float __v4sf __attribute__ ((__vector_size__ (16)));
typedef short __v8hi __attribute__ ((__vector_size__ (16)));
typedef unsigned short __v8hu __attribute__ ((__vector_size__ (16)));
typedef char __v16qi __attribute__ ((__vector_size__ (16)));
typedef signed char __v16qs __attribute__ ((__vector_size__ (16)));
typedef unsigned char __v16qu __attribute__ ((__vector_size__ (16)));
typedef long long __v1di __attribute__ ((__vector_size__ (8)));
typedef int __v2si __attribute__ ((__vector_size__ (8)));
typedef float __v2sf __attribute__ ((__vector_size__ (8)));
typedef short __v4hi __attribute__ ((__vector_size__ (8)));
typedef char __v8qi __attribute__ ((__vector_size__ (8)));
typedef long long __di;

/* Cache hints of __builtin_e2k_prefetch.  */
enum __e2k_hint
{
  E2K_HINT_NTA = 0,
  E2K_HINT_T2 = 1,
  E2K_HINT_T1 = 2,
  E2K_HINT_T0 = 3
};

/* The rounding argument of fdtoifd, fstoifs and their packed forms.  */
#define _TOIF_RC_NEAREST 0
#define _TOIF_RC_DOWN 1
#define _TOIF_RC_UP 2
#define _TOIF_RC_ZERO 3
#define _TOIF_RC_CURRENT 4
#define _TOIF_RC_IGNORE_INEXACT 8

/* Cache sizes, as lcc gives them by target.  */
#define E2K_SIZE_L1 65536
#if __iset__ == 4 || __iset__ == 5
#define E2K_SIZE_L2 524288
#elif __iset__ >= 7
#define E2K_SIZE_L2 1048576
#else
#define E2K_SIZE_L2 2097152
#endif
#define E2K_SIZE_L3 16777216
#define SIZE_L1 E2K_SIZE_L1
#define SIZE_L2 E2K_SIZE_L2
#if __iset__ == 4 || __iset__ == 5 || __iset__ >= 7
#define SIZE_L3 E2K_SIZE_L3
#endif

/* A prefetch with a cache hint: GCC's, which takes the hint as its
   locality (the same MAS as lcc's).  */
#define __builtin_e2k_prefetch(p, hint) \
  __builtin_prefetch ((const void *) (p), 0, (hint))

/* Write back and drop the line of P: lcc's code.  */
#define __builtin_e2k_clflush(p)					\
  __asm__ __volatile__ ("wait\tst_c = 1\n\tstd\t%0, 0x0, 0x0, mas=0xf\n\t"	\
			"wait\tfl_c = 1" :: "r" (p) : "memory")

/* Pointers and alignment; N a power of two.  */
#define E2K_ALIGN_PTR(p, n)						\
  ((__typeof__ (p)) (((unsigned long) (p) + (n) - 1)			\
		     & -(unsigned long) (n)))
#define E2K_ALIGN_PTR_BACK(p, n)					\
  ((__typeof__ (p)) ((unsigned long) (p) & -(unsigned long) (n)))
#define E2K_BYTES_TO_ALIGN(p, n) (-(unsigned long) (p) & ((n) - 1))
#define E2K_BYTES_FROM_ALIGN(p, n) ((unsigned long) (p) & ((n) - 1))

/* N = the leading or trailing zero bytes of the 64-bit X (8 for 0).  */
#define __CLZB(n, x) ((n) = __builtin_e2k_lzcntd (x) >> 3)
#define __CTZB(n, x)							\
  ((n) = __builtin_e2k_lzcntd (__builtin_e2k_bitrevd (x)) >> 3)
#define E2K_CLZB(n, x) __CLZB (n, x)
#define E2K_CTZB(n, x) __CTZB (n, x)

/* Misaligned data from two aligned words, S1 the lower, AL the byte
   offset 0-7: E2K_PREPARE_ALIGN makes SPEC, E2K_ALIGN_DATA sets DST to
   bytes AL ... AL + 7 of S2:S1.  The _BE forms take big-endian data, S1
   the earlier word.  */
#define E2K_PREPARE_ALIGN(al, spec)					\
  ((spec) = 0x0706050403020100ULL					\
	    + 0x0101010101010101ULL * (unsigned long long) (al))
#define E2K_ALIGN_DATA(s1, s2, dst, spec)				\
  ((dst) = __builtin_e2k_pshufb ((s2), (s1), (spec)))
#define E2K_PREPARE_ALIGN_BE(al, spec)					\
  ((spec) = 0x0f0e0d0c0b0a0908ULL					\
	    - 0x0101010101010101ULL * (unsigned long long) (al))
#define E2K_ALIGN_DATA_BE(s1, s2, dst, spec)				\
  ((dst) = __builtin_e2k_pshufb ((s1), (s2), (spec)))

/* The same by shifts: A a bit count (8 times the byte offset).  */
#define E2K_PREPARE_ALIGN_ARITH(ptr, a) ((a) = 8 * (a))
#define E2K_PREPARE_ALIGN_ARITH_BE(ptr, a) ((a) = 8 * (a))
#define E2K_ALIGN_DATA_ARITH(s1, s2, dst, a)				\
  ((dst) = (a) ? ((unsigned long long) (s1) >> (a))			\
		 | ((unsigned long long) (s2) << (64 - (a)))		\
	       : (unsigned long long) (s1))
#define E2K_ALIGN_DATA_ARITH_BE(s1, s2, dst, a)				\
  ((dst) = (a) ? ((unsigned long long) (s1) << (a))			\
		 | ((unsigned long long) (s2) >> (64 - (a)))		\
	       : (unsigned long long) (s1))

/* 32-bit words, byte offsets 0-3: A becomes a bit count, or (INSF32)
   512 times the byte offset, a field descriptor.  */
#define E2K_PREPARE_ALIGN_ARITH32(ptr, a) ((a) = 8 * (a))
#define E2K_ALIGN_DATA_ARITH32(s1, s2, dst, a)				\
  ((dst) = (a) ? ((unsigned int) (s1) >> (a))				\
		 | ((unsigned int) (s2) << (32 - (a)))			\
	       : (unsigned int) (s1))
#define E2K_PREPARE_ALIGN_INSF32(ptr, a) ((a) = 512 * (a))
#define E2K_ALIGN_DATA_INSF32(s1, s2, dst, a)				\
  E2K_ALIGN_DATA_ARITH32 (s1, s2, dst, (a) >> 6)

/* The FP control register %pfpfr.  */
#define __GETPFPFR(w) ((w) = __builtin_e2k_rrs_pfpfr ())
#define __SETPFPFR(w) __builtin_e2k_rws_pfpfr (w)

#if __iset__ >= 5
/* 16-byte forms: AL 0-15, DST bytes AL ... AL + 15 of the 32 bytes
   S2:S1; SPEC a qppermb mask.  */
#define E2K_PREPARE_ALIGN128(al, spec)					\
  ((spec) = __builtin_e2k_qppackdl					\
     (0x0f0e0d0c0b0a0908ULL						\
      + 0x0101010101010101ULL * (unsigned long long) (al),		\
      0x0706050403020100ULL						\
      + 0x0101010101010101ULL * (unsigned long long) (al)))
#define E2K_ALIGN_DATA128(s1, s2, dst, spec)				\
  ((dst) = __builtin_e2k_qppermb ((s2), (s1), (spec)))
#define E2K_PREPARE_ALIGN128_BE(al, spec)				\
  ((spec) = __builtin_e2k_qppackdl					\
     (0x1f1e1d1c1b1a1918ULL						\
      - 0x0101010101010101ULL * (unsigned long long) (al),		\
      0x1716151413121110ULL						\
      - 0x0101010101010101ULL * (unsigned long long) (al)))
#define E2K_ALIGN_DATA128_BE(s1, s2, dst, spec)				\
  ((dst) = __builtin_e2k_qppermb ((s1), (s2), (spec)))

/* D0 = {R0[0], R1[0]}, D1 = {R0[1], R1[1]}.  */
#define E2K_TRANSPOSE2_64F(r0, r1, d0, d1)				\
  do									\
    {									\
      __v2di __e2k_t0 = (__v2di) (r0), __e2k_t1 = (__v2di) (r1);	\
      (d0) = (__typeof__ (d0))						\
	__builtin_e2k_qppackdl (__e2k_t1[0], __e2k_t0[0]);		\
      (d1) = (__typeof__ (d1))						\
	__builtin_e2k_qppackdl (__e2k_t1[1], __e2k_t0[1]);		\
    }									\
  while (0)

/* Lane I of DJ = lane J of RI, 32-bit lanes.  */
#define E2K_TRANSPOSE4_32F(r0, r1, r2, r3, d0, d1, d2, d3)		\
  do									\
    {									\
      __v4si __e2k_a0 = (__v4si) (r0), __e2k_a1 = (__v4si) (r1);	\
      __v4si __e2k_a2 = (__v4si) (r2), __e2k_a3 = (__v4si) (r3);	\
      (d0) = (__typeof__ (d0)) (__v4si) { __e2k_a0[0], __e2k_a1[0],	\
					  __e2k_a2[0], __e2k_a3[0] };	\
      (d1) = (__typeof__ (d1)) (__v4si) { __e2k_a0[1], __e2k_a1[1],	\
					  __e2k_a2[1], __e2k_a3[1] };	\
      (d2) = (__typeof__ (d2)) (__v4si) { __e2k_a0[2], __e2k_a1[2],	\
					  __e2k_a2[2], __e2k_a3[2] };	\
      (d3) = (__typeof__ (d3)) (__v4si) { __e2k_a0[3], __e2k_a1[3],	\
					  __e2k_a2[3], __e2k_a3[3] };	\
    }									\
  while (0)
#endif

#include <e2kintrin-ops.h>

#endif /* _E2KINTRIN_H */
