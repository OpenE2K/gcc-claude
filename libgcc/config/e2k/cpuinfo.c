/* CPU identification data for lcc's __builtin_cpu_is (E2K).
   Written by Claude (Anthropic) for the experimental E2K port.

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

/* lcc compiles __builtin_cpu_is ("elbrus-vN") to a load of the 32-bit
   word at __cpu_info + 0 compared with N, and __builtin_cpu_is
   ("elbrus-<model>") to a load of __cpu_info + 4 compared with lcc's
   model code (seen in lcc 1.29.16 output).  lcc's own runtime fills the
   64-byte object in a priority 101 constructor.  MCST's glibc is built
   with lcc, and its static libc.a refers to __cpu_info (hidden) from
   dl-load.o, so a static link by GCC needs a definition.  */

struct e2k_cpu_info
{
  unsigned int iset;		/* 2..7, 0 if unknown */
  unsigned int model;		/* lcc's code for the CPU model */
  unsigned int reserved[14];
};

struct e2k_cpu_info __cpu_info __attribute__ ((visibility ("hidden")));

/* %idr model (bits 0-7; Linux arch/e2k/include/uapi/asm/bootinfo.h) to
   the instruction set and lcc's model code.  */
static const struct
{
  unsigned char idr_model, iset, lcc_model;
} e2k_models[] = {
  { 0x03, 3, 4 },		/* E2S: elbrus-4c */
  { 0x07, 4, 6 },		/* E8C: elbrus-8c */
  { 0x08, 4, 7 },		/* E1C+: elbrus-1c+ */
  { 0x09, 5, 8 },		/* E8C2: elbrus-8c2 */
  { 0x0a, 6, 9 },		/* E12C: elbrus-12c */
  { 0x0b, 6, 10 },		/* E16C: elbrus-16c */
  { 0x0c, 6, 11 },		/* E2C3: elbrus-2c3 */
  { 0x0e, 7, 13 },		/* E8V7: elbrus-8v7 */
};

void __attribute__ ((constructor (101)))
__cpu_init (void)
{
  unsigned long long idr;
  unsigned int i, model;

  if (__cpu_info.iset)
    return;
  __asm__ __volatile__ ("rrd %%idr, %0" : "=r" (idr));
  model = idr & 0xff;
  for (i = 0; i < sizeof e2k_models / sizeof e2k_models[0]; i++)
    if (e2k_models[i].idr_model == model)
      {
	__cpu_info.iset = e2k_models[i].iset;
	__cpu_info.model = e2k_models[i].lcc_model;
	return;
      }
  /* A virtual machine (model 0) or a CPU unknown here: the code is
     running, so the CPU has at least the instruction set it was built
     for.  */
  __cpu_info.iset = __iset__;
}
