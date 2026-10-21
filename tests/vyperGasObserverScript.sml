Theory vyperGasObserver
Ancestors
  callTrace vfmCompute vfmDecreasesGas vfmExecution vfmExecutionProp
  vfmContext vfmState vfmTypes arithmetic list option pair sum relation words
Libs
  cv_transLib

(* Source observations are selected by compiler-verified instruction PCs.
   Compiler-generated GAS instructions and descendant frames are not evidence. *)
Definition selected_gas_step_def:
  selected_gas_step d pcs s (r, s') =
    case (s.contexts, s'.contexts) of
      ((c,_)::_, (c',_)::_) =>
        if ISL r /\ LENGTH s.contexts = d /\ LENGTH s'.contexts = d /\
           next_opcode c = SOME Gas /\ MEM c.pc pcs
        then (case c'.stack of g::_ => SOME (w2n g) | [] => NONE)
        else NONE
    | _ => NONE
End

Definition selected_gas_tr_def:
  selected_gas_tr d pcs gs s (r, s') =
    let gs' = case selected_gas_step d pcs s (r, s') of
                NONE => gs | SOME g => g::gs in
    if ISR r \/ LENGTH s'.contexts < d then ((r,s'), REVERSE gs')
    else selected_gas_tr d pcs gs' s' (step s')
Termination
  WF_REL_TAC `inv_image ($< LEX ($< LEX $<))
    (\(d, pcs, gs, s, (r, s')).
      if ISR r \/ LENGTH s'.contexts < d then ((0:num), (0, 0))
      else (1, contexts_weight 0 s'.contexts))` >>
  rpt gen_tac >> strip_tac >>
  rename1 `step post` >>
  mp_tac (Q.SPEC `post` (REWRITE_RULE [decreases_gas_cred_def]
    decreases_gas_cred_step)) >>
  IF_CASES_TAC >- (
    rw[contexts_weight_def, unused_gas_def] >>
    gvs[step_def, handle_def, get_current_context_def, bind_def, fail_def] >>
    gvs[handle_step_def, reraise_def]) >>
  rw[] >> fs[LEX_DEF, UNCURRY] >>
  metis_tac[sum_CASES, ISL, ISR]
End

Definition selected_gas_execution_def:
  selected_gas_execution pcs es =
    selected_gas_tr (LENGTH es.contexts) pcs [] es (step es)
End

Definition selected_gas_readings_def:
  selected_gas_readings pcs es = SND (selected_gas_execution pcs es)
End

val () = cv_auto_trans next_opcode_def;
val () = cv_auto_trans selected_gas_step_def;
val selected_gas_tr_pre_def =
  cv_trans_pre "selected_gas_tr_pre" selected_gas_tr_def;

Theorem selected_gas_tr_pre[cv_pre]:
  !d pcs gs s rs. selected_gas_tr_pre d pcs gs s rs
Proof
  simp[FORALL_PROD] >> recInduct selected_gas_tr_ind >> rw[] >>
  rw[Once selected_gas_tr_pre_def]
QED

val selected_gas_execution_pre_def =
  cv_trans_pre "selected_gas_execution_pre" selected_gas_execution_def;

Theorem selected_gas_execution_pre[cv_pre]:
  !pcs es. selected_gas_execution_pre pcs es
Proof
  simp[selected_gas_execution_pre_def, selected_gas_tr_pre]
QED

val () = cv_auto_trans selected_gas_readings_def;
