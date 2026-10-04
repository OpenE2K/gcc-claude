/* Prototypes for the Elbrus (E2K) port.
   Written by Claude (Anthropic) as an experiment; see README.claude.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published
   by the Free Software Foundation; either version 3, or (at your
   option) any later version.  */

#ifndef GCC_E2K_PROTOS_H
#define GCC_E2K_PROTOS_H

extern HOST_WIDE_INT e2k_initial_elimination_offset (int, int);
extern int e2k_reg_parm_stack_space (const_tree);
extern void e2k_expand_prologue (void);
extern void e2k_expand_epilogue (void);
extern const char *e2k_asm_output_opcode (FILE *, const char *);
extern const char *e2k_output_setwd (void);
extern const char *e2k_output_call (void);
extern int e2k_window_base (void);

#ifdef RTX_CODE
extern void e2k_init_cumulative_args (CUMULATIVE_ARGS *, tree, rtx, tree,
				      bool);
extern void e2k_final_prescan_insn (rtx_insn *);
extern bool e2k_expand_move (machine_mode, rtx *);
extern void e2k_expand_call (rtx, rtx, rtx, rtx);
extern bool e2k_legitimate_address_p (machine_mode, rtx, bool);
extern bool e2k_legitimate_constant_p (machine_mode, rtx);
extern void e2k_split_double_move (rtx, rtx);
extern rtx e2k_cmp_op (enum rtx_code, machine_mode, rtx, rtx, bool *);
extern void e2k_split_compare_branch (rtx *, machine_mode);
extern void e2k_split_cstore (rtx *, machine_mode);
extern void e2k_split_movcc (rtx *, machine_mode);
extern bool e2k_lower_quiet_fp_cmp (rtx *, rtx *, rtx *, machine_mode);
extern void e2k_expand_save_stack_nonlocal (rtx);
extern void e2k_expand_nonlocal_goto (rtx, rtx);
extern bool e2k_expand_movcc (rtx *);
extern bool e2k_tls_symbol_p (rtx);
extern bool e2k_symbolic_operand_p (rtx);
extern int e2k_insn_lits (rtx_insn *);
extern rtx e2k_barrier_mem (void);
extern rtx e2k_return_addr (int, rtx);
extern rtx e2k_atomic_mem (rtx);
#endif

#endif /* GCC_E2K_PROTOS_H */
