/* C and C++ front-end support for the Elbrus (E2K) port: lcc's pragmas.
   Written by Claude (Anthropic) as an experiment, from the relcc2
   specification; see gcc/config/e2k/README.claude.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published
   by the Free Software Foundation; either version 3, or (at your
   option) any later version.

   GCC is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
   License for more details.

   You should have received a copy of the GNU General Public License
   along with GCC; see the file COPYING3.  If not see
   <http://www.gnu.org/licenses/>.  */

#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tm.h"
#include "c-family/c-common.h"
#include "cpplib.h"
#include "c-family/c-pragma.h"
#include "tm_p.h"

/* A pragma of lcc's that only gives hints this compiler doesn't use.  */
static void
e2k_pragma_ignore (cpp_reader *)
{
}

/* lcc's pragmas (spec/abi/source-compat.md, "Pragmas"), which glibc's
   and the kernel's E2K code use under -Wall -Werror.  lcc's `ivdep',
   `novector' and `unroll (N)' mean what GCC's `GCC ivdep', `GCC
   novector' and `GCC unroll N' do, so they become those.  The others are
   hints for lcc's own optimizations and are dropped by the preprocessor
   (as Darwin's `mark'), which leaves no token for the parser: glibc and
   the kernel write them between `unroll (N)' or `ivdep' and the loop
   (`#pragma unroll (2)', `#pragma loop count (100)', `for'), where GCC's
   parser takes only its own loop pragmas.  Nothing is registered for
   -E, so preprocessed output keeps them all.  */
void
e2k_register_pragmas (void)
{
  static const char *const ignored[] = {
    /* Loops: `loop count (N)' (also `loop_count'), array prefetch,
       vectorizing hints, data speculation, pipelining.  */
    "loop", "loop_count", "noprefetch", "prefetch", "vector", "no_dam",
    "no_rtmd", "swp", "noswp", "comb_oper", "no_comb_oper", "cache_opt",
    "no_cache_opt", "reduce", "spmv", "nonesting", "split_fuse",
    "apb_cache", "apb_aligned",
    /* Scheduling of the next asm.  */
    "asm_inline", "no_asm_inline", "asm_length",
    /* EDG's diagnostics, by number.  */
    "diag_suppress", "diag_remark", "diag_warning", "diag_error",
    "diag_default", "diag_once",
    /* Deprecated forms of attributes.  */
    "unknown_control_flow", "no_inline", "hot", "no_side_effect",
    "no_instrument_function", "no_profile_instrument_function"
  };

  if (flag_preprocess_only)
    return;
  cpp_register_deferred_pragma (parse_in, NULL, "ivdep", PRAGMA_IVDEP,
				false, false);
  cpp_register_deferred_pragma (parse_in, NULL, "novector",
				PRAGMA_NOVECTOR, false, false);
  cpp_register_deferred_pragma (parse_in, NULL, "unroll", PRAGMA_UNROLL,
				false, false);
  for (const char *name : ignored)
    cpp_register_pragma (parse_in, NULL, name, e2k_pragma_ignore, false);
}
