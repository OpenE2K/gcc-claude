/* Linux definitions for the Elbrus (E2K) port.
   Written by Claude (Anthropic) as an experiment; see README.claude.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published
   by the Free Software Foundation; either version 3, or (at your
   option) any later version.  */

#ifndef GCC_E2K_LINUX_H
#define GCC_E2K_LINUX_H

#define TARGET_OS_CPP_BUILTINS() GNU_USER_TARGET_OS_CPP_BUILTINS ()

/* spec/abi/elf.md.  */
#define GLIBC_DYNAMIC_LINKER "/lib64/ld-linux.so.2"

/* lcc's -pthread defines _REENTRANT; configure scripts test for it.  */
#undef CPP_SPEC
#define CPP_SPEC "%{pthread:-D_REENTRANT}"

#undef ASM_SPEC
#define ASM_SPEC \
  "%{mtune=*:-mcpu=%*;march=elbrus-v*:-mcpu=elbrus-v%*;:-mcpu=elbrus-v3}"

#undef LINK_SPEC
#define LINK_SPEC "%{h*}			\
   %{static:-Bstatic}				\
   %{shared:-shared}				\
   %{symbolic:-Bsymbolic}			\
   %{!static:%{!static-pie:			\
     %{rdynamic:-export-dynamic}		\
     %{!shared:-dynamic-linker " GNU_USER_DYNAMIC_LINKER "}}} \
   %{static-pie:-Bstatic -pie --no-dynamic-linker -z text}"

/* MCST's crtfastmath.o sets flush to zero and denormals are zero in
   %pfpfr (spec/abi/registers.md, "Flush to zero"); lcc links it for
   these options, into shared objects too.  */
#undef ENDFILE_SPEC
#define ENDFILE_SPEC							\
  "%{Ofast|ffast-math|funsafe-math-optimizations:crtfastmath.o%s} "	\
  GNU_USER_TARGET_ENDFILE_SPEC

/* lcc emits no PT_GNU_STACK note; keep the default (no note) too.  */

#endif /* GCC_E2K_LINUX_H */
