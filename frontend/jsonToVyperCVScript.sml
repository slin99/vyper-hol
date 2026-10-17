Theory jsonToVyperCV
Ancestors
  jsonToVyper jsonToVyperTopLevel jsonToVyperExprCV list option
Libs
  cv_transLib

(* Preserve the source frontend's defined-input conditions, rather than
   choosing a value for its undefined empty interface-constructor case. *)
val translate_var_mutability_pre_def = cv_auto_trans_pre
  "translate_var_mutability_pre" translate_var_mutability_def;

Theorem translate_stmt_list_map:
  translate_stmt_list ctx stmts = MAP (translate_stmt ctx) stmts
Proof
  simp[translate_stmt_list_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

val translate_toplevel_compute = save_thm ("translate_toplevel_compute",
  PURE_REWRITE_RULE [GSYM translate_expr_list_map, GSYM translate_stmt_list_map]
    translate_toplevel_def);
val translate_toplevel_pre_def = cv_auto_trans_pre
  "translate_toplevel_pre" translate_toplevel_compute;

Definition translate_toplevels_def:
  translate_toplevels ni im ec tc nr declaration_only tops =
    MAP (λtop. if declaration_only ∧ is_function_toplevel top then NONE
               else translate_toplevel ni im ec tc nr top) tops
End

Theorem translate_toplevels_compute:
  (translate_toplevels ni im ec tc nr declaration_only [] = []) /\
  (translate_toplevels ni im ec tc nr declaration_only (top::tops) =
    (if declaration_only ∧ is_function_toplevel top then NONE
     else translate_toplevel ni im ec tc nr top) ::
    translate_toplevels ni im ec tc nr declaration_only tops)
Proof
  simp[translate_toplevels_def]
QED

val translate_toplevels_pre_def = cv_auto_trans_pre
  "translate_toplevels_pre" translate_toplevels_compute;

Theorem translate_toplevels_implementation:
  translate_toplevels ni im ec tc nr F tops =
    MAP (translate_toplevel ni im ec tc nr) tops
Proof
  simp[translate_toplevels_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

val translate_module_compute = save_thm ("translate_module_compute",
  PURE_REWRITE_RULE [GSYM translate_toplevels_implementation] translate_module_def);
val translate_module_pre_def = cv_auto_trans_pre
  "translate_module_pre" translate_module_compute;
val translate_imported_module_compute = save_thm ("translate_imported_module_compute",
  PURE_REWRITE_RULE [GSYM translate_toplevels_def] translate_imported_module_def);
val translate_imported_module_pre_def = cv_auto_trans_pre
  "translate_imported_module_pre" translate_imported_module_compute;
val translate_imported_modules_pre_def = cv_auto_trans_pre
  "translate_imported_modules_pre" translate_imported_modules_def;
val translate_annotated_ast_canonical_pre_def = cv_auto_trans_pre
  "translate_annotated_ast_canonical_pre" translate_annotated_ast_canonical_def;
val translate_annotated_ast_pre_def = cv_auto_trans_pre
  "translate_annotated_ast_pre" translate_annotated_ast_def;
