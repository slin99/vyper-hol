Theory jsonToVyperExprCV
Ancestors
  jsonToVyperExpr jsonToVyperTypeCV jsonAST vyperAST list option cv cv_rep
Libs
  cv_transLib jsonToVyperCVLib

(* Eliminate higher-order recursive OPTION_MAP specializations without changing
   which optional operands are translated. *)
Theorem OPTION_MAP_as_case:
  OPTION_MAP f x = case x of NONE => NONE | SOME y => SOME (f y)
Proof
  Cases_on `x` >> simp[]
QED

(* HD [] in interface_constructor_result is intentionally not assigned a
   fabricated value. Keep its defined-input condition in the CV theorems;
   the shared JSON importer rejects empty interface-constructor calls. *)
val interface_constructor_result_pre_def = cv_auto_trans_pre
  "interface_constructor_result_pre" interface_constructor_result_def;
val translate_module_call_pre_def = cv_auto_trans_pre
  "translate_module_call_pre" translate_module_call_def;
val translate_call_pre_def = cv_auto_trans_pre
  "translate_call_pre" translate_call_def;

val translate_expr_compute = save_thm ("translate_expr_compute",
  PURE_REWRITE_RULE [OPTION_MAP_as_case] translate_expr_def);

val translate_expr_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "translate_expr_exec"
    translate_expr_compute
    (WF_REL_TAC `measure (λx. case x of
       | INL (_, e) => json_expr_size e
       | INR (INL (_, es)) => list_size json_expr_size es
       | INR (INR (_, kws)) => list_size json_keyword_size kws)` >>
     rw[] >>
     imp_res_tac find_keyword_size >>
     imp_res_tac call_pop_index_size >>
     gvs[] >>
     drule is_raw_call_calldata_call_nonempty >>
     Cases_on `args` >> gvs[]);

val () = cv_auto_trans find_keyword_def;
val () = cv_auto_trans call_pop_index_def;
fun cv_equation name =
  case DefnBase.lookup_userdef
    (prim_mk_const {Thy = current_theory (), Name = name}) of
    SOME {thm = DefnBase.STDEQNS th,...} => th
  | _ => raise Fail ("missing CV equation: " ^ name);
val keyword_cv_def = cv_equation "cv_find_keyword";
val pop_index_cv_def = cv_equation "cv_call_pop_index";

Theorem cv_snd_if_size_bound:
  cv_size (cv_snd a) ≤ n ∧ cv_size (cv_snd b) ≤ n ⇒
  cv_size (cv_snd (cv_if p a b)) ≤ n
Proof
  rw[cv_if_def0]
QED

Theorem cv_find_keyword_size:
  cv_size (cv_snd (cv_find_keyword name kws)) ≤ cv_size kws
Proof
  Induct_on `kws` >- simp[Once keyword_cv_def, cv_if_def] >>
  rename1 `cv_find_keyword name (cv$Pair head tail)` >>
  Cases_on `head` >>
  simp[Once keyword_cv_def, cv_if_def] >>
  rw[] >> simp[]
QED

Theorem cv_call_pop_index_size:
  cv_size (cv_snd (cv_call_pop_index v)) ≤ cv_size v
Proof
  rewrite_tac[pop_index_cv_def] >>
  rpt (irule cv_snd_if_size_bound >> conj_tac) >>
  simp[] >>
  cv_termination_tac
QED

Theorem cv_find_keyword_pair_size:
  cv_find_keyword name kws = cv$Pair a b ⇒ cv_size b ≤ cv_size kws
Proof
  strip_tac >>
  `cv_size (cv_snd (cv_find_keyword name kws)) ≤ cv_size kws`
    by irule cv_find_keyword_size >>
  gvs[]
QED

Theorem cv_call_pop_index_pair_size:
  cv_call_pop_index v = cv$Pair a b ⇒ cv_size b ≤ cv_size v
Proof
  strip_tac >>
  `cv_size (cv_snd (cv_call_pop_index v)) ≤ cv_size v`
    by irule cv_call_pop_index_size >>
  gvs[]
QED

val translate_expr_pre_def = cv_auto_trans_pre_rec
  "translate_expr_pre translate_expr_list_pre translate_kwargs_pre"
  translate_expr_compute
  (WF_REL_TAC `measure (λx. case x of
     | INL (_, e) => cv_size e
     | INR (INL (_, es)) => cv_size es
     | INR (INR (_, kws)) => cv_size kws)` >>
   cv_termination_tac >>
   imp_res_tac cv_find_keyword_pair_size >>
   imp_res_tac cv_call_pop_index_pair_size >>
   first_assum (fn th =>
     match_mp_tac (MATCH_MP
       (REWRITE_RULE [GSYM AND_IMP_INTRO] arithmeticTheory.LESS_EQ_LESS_TRANS)
       th)) >>
   cv_termination_tac);

Theorem translate_expr_list_map:
  translate_expr_list ctx es = MAP (translate_expr ctx) es
Proof
  Induct_on `es` >> simp[translate_expr_def]
QED

(* These list helpers expose the original nested MAP recursions as ordinary
   mutually recursive equations. Their definitions retain an explicit bridge
   to the original logical API. *)
val translate_base_target_pre_def = cv_auto_trans_pre
  "translate_base_target_pre" translate_base_target_def;

Definition translate_target_list_def:
  translate_target_list ctx tgts = MAP (λtgt. translate_target ctx tgt) tgts
End

Theorem translate_target_list_compute:
  (translate_target_list ctx [] = []) /\
  (translate_target_list ctx (tgt::tgts) =
    translate_target ctx tgt :: translate_target_list ctx tgts)
Proof
  simp[translate_target_list_def]
QED

val translate_target_compute = save_thm ("translate_target_compute",
  CONJ (PURE_REWRITE_RULE [GSYM translate_target_list_def]
          translate_target_def)
       translate_target_list_compute);

val translate_target_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "translate_target_exec"
    translate_target_compute
    (WF_REL_TAC `measure (λx. case x of
       | INL (_, tgt) => json_target_size tgt
       | INR (_, tgts) => list_size json_target_size tgts)` >> simp[]);

val translate_target_pre_def = cv_auto_trans_pre
  "translate_target_pre translate_target_list_pre" translate_target_compute;

val translate_iter_pre_def = cv_auto_trans_pre
  "translate_iter_pre" translate_iter_def;

Definition translate_stmt_list_def:
  translate_stmt_list ctx stmts = MAP (λstmt. translate_stmt ctx stmt) stmts
End

Theorem translate_stmt_list_compute:
  (translate_stmt_list ctx [] = []) /\
  (translate_stmt_list ctx (stmt::stmts) =
    translate_stmt ctx stmt :: translate_stmt_list ctx stmts)
Proof
  simp[translate_stmt_list_def]
QED

val translate_stmt_compute = save_thm ("translate_stmt_compute",
  CONJ (PURE_REWRITE_RULE
          [GSYM translate_stmt_list_def, GSYM translate_expr_list_map]
          translate_stmt_def)
       translate_stmt_list_compute);

val translate_stmt_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "translate_stmt_exec"
    translate_stmt_compute
    (WF_REL_TAC `measure (λx. case x of
       | INL (_, stmt) => json_stmt_size stmt
       | INR (_, stmts) => list_size json_stmt_size stmts)` >>
     rw[] >> simp[json_stmt_size_def]);

val translate_stmt_pre_def = cv_auto_trans_pre
  "translate_stmt_pre translate_stmt_list_pre" translate_stmt_compute;
