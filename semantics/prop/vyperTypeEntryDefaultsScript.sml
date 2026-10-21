(*
 * Default arguments of a checked external entry: they either evaluate to
 * values of the remaining parameters' types, or one of them fails at run time
 * with an error of its own evaluation; on success the arguments bind.
 *
 * Vyper accepts any RUNTIME_CONSTANT default (e.g. `msg.value - 1`), which can
 * revert at call time, so success is not a theorem.  The failing default is
 * characterised by its own `eval_expr` result: either a runtime error that is
 * not a TypeError, or a storage array reference, which `evaluate_defaults`
 * does not materialise.
 *
 * The entry is the tuple selected by `lookup_exported_function` from the
 * initial call context, as in `call_external`.
 *
 * TOP-LEVEL:
 * - checked_selected_entry_defaults_cases
 * - checked_selected_entry_bind_arguments
 *
 * Helper:
 * - evaluate_defaults_error_stop
 * - evaluate_defaults_typed_cases
 * - defaults_env_function_entry_env
 * - checked_entry_defaults_env_consistent
 * - checked_public_getter_args_well_formed
 *)

Theory vyperTypeEntryDefaults
Ancestors
  list rich_list arithmetic finite_map option pair
  vyperAST vyperValue vyperState vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues
  vyperTypeExprSoundness vyperTypeExprResult vyperTypeInitialState
  vyperTypeEvalSoundness vyperTypeCallGraph vyperTypeCallGraphSoundness
  vyperTypeCallStackSoundness vyperTypeBindArguments
  vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeContractFunction vyperTypeContractGetter
  vyperTypeEntryReadiness vyperTypeContractSoundness

val _ = Parse.hide "body";

(* ===== Evaluating a list of well-typed defaults ===== *)

(* The successful prefix threads its exact remaining observations to the
 * first failing default, whose singleton evaluation determines the error
 * and remaining evidence. *)
Theorem evaluate_defaults_error_stop:
  !es gs err gs_rest.
    evaluate_defaults cx am gs es = (INR err,gs_rest) ==>
    ?pre pre_vs gs_at e post.
      es = pre ++ e::post /\
      evaluate_defaults cx am gs pre = (INL pre_vs,gs_at) /\
      evaluate_defaults cx am gs_at [e] = (INR err,gs_rest) /\
      !v. FST (eval_expr cx e
        (initial_state am [FEMPTY] with gas_observations := gs_at)) <>
        INL (Value v)
Proof
  Induct >- simp[evaluate_defaults_def] >>
  rpt gen_tac >>
  simp[Once evaluate_defaults_def] >>
  Cases_on `eval_expr cx h
    (initial_state am [FEMPTY] with gas_observations := gs)` >>
  rename1 `eval_expr cx h _ = (head_res,head_st)` >>
  Cases_on `head_res`
  >- (rename1 `eval_expr cx h _ = (INL head_tv,head_st)` >>
      Cases_on `head_tv` >> simp[] >> rpt strip_tac >>
      TRY (qexistsl [`[]`,`[]`,`gs`,`h`,`es`] >>
           simp[evaluate_defaults_def] >> NO_TAC) >>
      rename1 `eval_expr cx h _ = (INL (Value head_v),head_st)` >>
      Cases_on `evaluate_defaults cx am head_st.gas_observations es` >>
      gvs[AllCaseEqs()] >>
      first_x_assum drule >> strip_tac >>
      qexistsl [`h::pre`,`head_v::pre_vs`,`gs_at`,`e`,`post`] >>
      simp[evaluate_defaults_def]) >>
  rpt strip_tac >>
  qexistsl [`[]`,`[]`,`gs`,`h`,`es`] >>
  simp[evaluate_defaults_def]
QED

(* A well-typed default whose evaluation is not a value either raised a
 * non-TypeError exception or yielded a storage array reference; HashMap
 * references are excluded by its type. *)
Theorem default_eval_not_value_cases[local]:
  well_typed_expr env e /\
  (!tyv. evaluate_type env.type_defs (expr_type e) = SOME tyv ==> tyv <> NoneTV) /\
  env_consistent env cx (initial_state am [FEMPTY] with gas_observations := gs) /\
  state_well_typed (initial_state am [FEMPTY] with gas_observations := gs) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!v. FST (eval_expr cx e
    (initial_state am [FEMPTY] with gas_observations := gs)) <> INL (Value v)) ==>
  (?err. FST (eval_expr cx e
     (initial_state am [FEMPTY] with gas_observations := gs)) = INR err /\
         no_type_error_result (INR err : toplevel_value + exception)) \/
  (?is_transient slot elem_tv bd.
     FST (eval_expr cx e
       (initial_state am [FEMPTY] with gas_observations := gs)) =
       INL (ArrayRef is_transient slot elem_tv bd))
Proof
  strip_tac >>
  `accounts_well_typed
    (initial_state am [FEMPTY] with gas_observations := gs).accounts` by
    simp[initial_state_def] >>
  Cases_on `eval_expr cx e
    (initial_state am [FEMPTY] with gas_observations := gs)` >>
  rename1 `eval_expr cx e _ = (res1,st1)` >>
  drule_all (cj 8 eval_all_type_sound_mutual) >> strip_tac >>
  Cases_on `res1` >> gvs[] >>
  rename1 `expr_result_typed env e tv` >>
  Cases_on `tv` >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, toplevel_value_typed_def]
QED

Theorem well_typed_exprs_MEM[local]:
  !es. well_typed_exprs env es /\ MEM e es ==> well_typed_expr env e
Proof
  Induct >> rw[well_typed_expr_def] >> gvs[]
QED

(* Successful defaults are typed; a failure is explained by the actual
 * failing expression at the evidence suffix left by its successful prefix. *)
Theorem evaluate_defaults_typed_cases:
  well_typed_exprs env es /\
  (!e tyv. MEM e es /\ evaluate_type env.type_defs (expr_type e) = SOME tyv ==>
     tyv <> NoneTV) /\
  (!gs. env_consistent env cx
    (initial_state am [FEMPTY] with gas_observations := gs)) /\
  (!gs. state_well_typed
    (initial_state am [FEMPTY] with gas_observations := gs)) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e. MEM e es ==> call_evaluation_safe cx (int_calls_expr e)) ==>
  (?vs gs_rest.
     evaluate_defaults cx am gs es = (INL vs,gs_rest) /\
     LIST_REL
       (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                   value_has_type tv v)
       vs es) \/
  (?err gs_rest pre pre_vs gs_at e post.
   evaluate_defaults cx am gs es = (INR err,gs_rest) /\
   es = pre ++ e::post /\
   evaluate_defaults cx am gs pre = (INL pre_vs,gs_at) /\
   evaluate_defaults cx am gs_at [e] = (INR err,gs_rest) /\
   ((?exc. FST (eval_expr cx e
       (initial_state am [FEMPTY] with gas_observations := gs_at)) = INR exc /\
             no_type_error_result (INR exc : toplevel_value + exception)) \/
    (?is_transient slot elem_tv bd.
       FST (eval_expr cx e
         (initial_state am [FEMPTY] with gas_observations := gs_at)) =
         INL (ArrayRef is_transient slot elem_tv bd))))
Proof
  strip_tac >>
  Cases_on `evaluate_defaults cx am gs es` >>
  rename1 `evaluate_defaults cx am gs es = (defaults_res,gs_rest)` >>
  Cases_on `defaults_res`
  >- (disj1_tac >> simp[] >>
      drule_all evaluate_defaults_success_values_typed >> simp[]) >>
  rename1 `evaluate_defaults cx am gs es = (INR err,gs_rest)` >>
  disj2_tac >>
  drule evaluate_defaults_error_stop >> strip_tac >>
  qexistsl [`err`,`gs_rest`,`pre`,`pre_vs`,`gs_at`,`e`,`post`] >>
  simp[] >>
  `MEM e es` by simp[] >>
  irule default_eval_not_value_cases >> simp[] >>
  qexists_tac `env` >> simp[] >>
  metis_tac[well_typed_exprs_MEM]
QED

(* The typed values of the needed defaults are typed against the parameters
 * they fill. *)
Theorem defaults_values_typed_args[local]:
  LIST_REL
    (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                value_has_type tv v)
    vs es /\
  MAP expr_type es = MAP SND params ==>
  args_values_typed tenv params vs
Proof
  rw[args_values_typed_def, listTheory.LIST_REL_EL_EQN]
  >- metis_tac[listTheory.LENGTH_MAP] >>
  `LENGTH params = LENGTH es` by metis_tac[listTheory.LENGTH_MAP] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `expr_type (EL i es) = SND (EL i params)` by
    metis_tac[listTheory.EL_MAP] >>
  gvs[]
QED

(* As intcall_needed_defaults_param_types, but for provided arguments of any
 * type (an external entry's are values, not expressions). *)
Theorem needed_defaults_param_types[local]:
  MAP expr_type dflts =
    MAP SND (DROP (LENGTH params - LENGTH dflts) (params:argument list)) /\
  LENGTH vals <= LENGTH params /\
  LENGTH params - LENGTH vals <= LENGTH dflts ==>
  MAP expr_type (DROP (LENGTH dflts - (LENGTH params - LENGTH vals)) dflts) =
  MAP SND (DROP (LENGTH vals) params)
Proof
  strip_tac >>
  `LENGTH dflts <= LENGTH params` by
    metis_tac[intcall_defaults_map_param_types_length_le] >>
  simp[listTheory.MAP_DROP, rich_listTheory.DROP_DROP_T] >>
  `LENGTH params - LENGTH dflts +
     (LENGTH dflts - (LENGTH params - LENGTH vals)) = LENGTH vals` by
    decide_tac >>
  simp[]
QED


(* Defaults dichotomy: under a checked contract, the needed default suffix of
 * the selected entry either evaluates to values of the remaining parameters'
 * types, or `evaluate_defaults` stops at a default `e`: every default before
 * it evaluated to a value, and `e`'s own evaluation fails with a runtime error
 * that is not a TypeError, or yields a storage array reference (which
 * `evaluate_defaults` does not materialise). *)
Theorem checked_selected_entry_defaults_cases:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts ==>
  (?vs gs_rest.
     evaluate_defaults cx am gs
       (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) =
       (INL vs,gs_rest) /\
     args_values_typed (type_env_all_modules mods)
       (DROP (LENGTH tx.args) args) vs) \/
  (?err gs_rest pre pre_vs gs_at e post.
   evaluate_defaults cx am gs
     (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) =
     (INR err,gs_rest) /\
   DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts =
     pre ++ e::post /\
   evaluate_defaults cx am gs pre = (INL pre_vs,gs_at) /\
   evaluate_defaults cx am gs_at [e] = (INR err,gs_rest) /\
   ((?exc. FST (eval_expr cx e
       (initial_state am [FEMPTY] with gas_observations := gs_at)) = INR exc /\
             no_type_error_result (INR exc : toplevel_value + exception)) \/
    (?is_transient slot elem_tv bd.
       FST (eval_expr cx e
         (initial_state am [FEMPTY] with gas_observations := gs_at)) =
         INL (ArrayRef is_transient slot elem_tv bd))))
Proof
  strip_tac >>
  drule_all checked_selected_entry_defaults_setup >> strip_tac >>
  drule_all checked_entry_defaults_env_consistent >> strip_tac >>
  qabbrev_tac `needed = DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts` >>
  `MAP expr_type needed = MAP SND (DROP (LENGTH tx.args) args)` by
    (qunabbrev_tac `needed` >> irule needed_defaults_param_types >> simp[]) >>
  mp_tac (Q.INST [`env` |-> `artifact_env art mods src`, `es` |-> `needed`]
            evaluate_defaults_typed_cases) >>
  impl_tac
  >- (simp[Abbr `needed`, well_typed_exprs_DROP] >>
      simp[artifact_env_def] >>
      metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  strip_tac
  >- (disj1_tac >> qexistsl [`vs`,`gs_rest`] >> simp[] >>
      irule defaults_values_typed_args >>
      qexists_tac `needed` >> gvs[artifact_env_def]) >>
  disj2_tac >> simp[] >> metis_tac[]
QED



(* Binding corollary: when the needed defaults evaluate, the provided and
 * default values bind to the selected parameters and are typed by them. *)
Theorem checked_selected_entry_bind_arguments:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  provided_args_typed (type_env_all_modules mods) args tx.args /\
  evaluate_defaults cx am gs
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) =
    (INL dflt_vs,gs_rest) ==>
  ?scope.
    bind_arguments (type_env_all_modules mods) args (tx.args ++ dflt_vs) =
      SOME scope /\
    args_values_typed (type_env_all_modules mods) args (tx.args ++ dflt_vs)
Proof
  strip_tac >>
  drule_all checked_selected_entry_defaults_setup >> strip_tac >>
  drule_all checked_entry_defaults_env_consistent >> strip_tac >>
  `checked_call_inputs_ready (type_env_all_modules mods) cx am gs args dflts tx.args` by
    simp[checked_call_inputs_ready_def, checked_defaults_ready_def] >>
  mp_tac (Q.INST [`tenv` |-> `type_env_all_modules mods`,
                  `params` |-> `args`, `vals` |-> `tx.args`,
                  `env` |-> `artifact_env art mods src`]
           checked_call_inputs_ready_bind_arguments) >>
  impl_tac
  >- (simp[artifact_env_def, well_typed_exprs_DROP] >>
      metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  strip_tac >> gvs[]
QED
