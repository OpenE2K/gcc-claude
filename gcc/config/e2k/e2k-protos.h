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
extern bool e2k_partial_subreg_p (const_rtx);
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
extern const char *e2k_output_spec_load (rtx *, bool);
extern const char *e2k_output_mova (rtx *);
extern const char *e2k_output_prefetch (void);
extern const char *e2k_output_hwloop_end_wide (rtx_insn *, rtx *);
extern const char *e2k_output_hwloop_end (rtx_insn *);
extern const char *e2k_output_ct_pred (rtx_insn *);
extern const char *e2k_output_ldchk_jump (rtx *);
struct ce_if_block;
extern void e2k_ifcvt_modify_tests (struct ce_if_block *, rtx *, rtx *);
extern const char *e2k_output_setbn (int, int);
extern bool e2k_doloop_declined_p (rtx);
extern bool e2k_doloop_wide;
extern bool e2k_dbl_p (void);
extern void e2k_expand_save_stack_nonlocal (rtx);
extern void e2k_expand_nonlocal_goto (rtx, rtx);
extern bool e2k_expand_movcc (rtx *);
extern bool e2k_tls_symbol_p (rtx);
extern bool e2k_symbolic_operand_p (rtx);
extern int e2k_insn_lits (rtx_insn *);
extern rtx e2k_barrier_mem (void);
extern rtx e2k_return_addr (int, rtx);
extern rtx e2k_atomic_mem (rtx);
extern void e2k_expand_vec_cmp (rtx, enum rtx_code, rtx, rtx);
extern void e2k_expand_vec_duplicate (rtx, rtx);
extern void e2k_expand_vec_init (rtx, rtx);
extern void e2k_expand_vec_extract (rtx, rtx, int);
extern void e2k_expand_vec_unpack (rtx, rtx, bool, bool);
extern void e2k_expand_vec_pack_trunc (rtx, rtx, rtx);
extern void e2k_split_bswap (rtx, rtx, rtx);
extern bool e2k_bswap_mem_p (rtx);
extern bool e2k_getf_field_p (machine_mode, rtx, rtx);
extern rtx e2k_bit_test (machine_mode, rtx, rtx, rtx);
extern const char *e2k_output_getf (rtx *, bool);
extern const char *e2k_output_getfs (rtx *);
extern int e2k_lowmask_bits (rtx);
extern const char *e2k_output_lowmask (rtx *);
extern bool e2k_insf_mask_p (machine_mode, rtx, rtx);
extern const char *e2k_output_insf (rtx *, machine_mode);
extern void e2k_expand_floatunsdi (rtx, rtx);
#endif

extern bool e2k_epilogue_uses (unsigned);

#endif /* GCC_E2K_PROTOS_H */
