Theory vyperGasReplayTest
Ancestors
  vyperTestRunner vyperGasObserver vyperInterpreter vyperState vyperContext
  vyperAST vyperValue contractABI vfmTypes vfmState vfmExecution
  list finite_map words pair
Libs
  cv_transLib wordsLib

Definition gas_test_source_def:
  gas_test_source =
    [FunctionDecl External View F F "read" [] [] (BaseT (UintT 256))
      [Return (SOME (Builtin (BaseT (UintT 256)) (Env MsgGas) []))]]
End

Definition gas_test_machine_def:
  gas_test_machine code = initial_machine_state with
    <| accounts := update_account 32w (empty_account_state with code := code)
                     initial_machine_state.accounts;
       sources := [(32w, [(NONE, gas_test_source)])] |>
End

Definition gas_test_call_def:
  gas_test_call = <| sender := 33w; target := 32w; callData := []; value := 0;
    timeStamp := 1; blockNumber := 1; blockHashes := []; blobHashes := [];
    blobBaseFee := 1; gasLimit := 50000; blockGasLimit := 10000000000;
    gasPrice := 0; chainId := 1; static := F;
    expectedOutput := SOME (REPLICATE 30 0w ++ [113w;70w]) |>
End

Definition gas_test_selectors_def:
  gas_test_selectors : (byte list # string # abi_type list # abi_type list) list =
    [([], ("read", [], [Uint 256]))]
End

val () = cv_auto_trans gas_test_source_def;
val () = cv_auto_trans gas_test_machine_def;
val () = cv_auto_trans gas_test_call_def;
val () = cv_auto_trans gas_test_selectors_def;

(* GAS costs two units after the genuine 21000-unit transaction intrinsic
   charge; no expected-output bytes are consulted by the evidence producer. *)
Theorem concrete_transaction_gas_observation:
  source_gas_evidence [0]
    (gas_test_machine [90w;95w;82w;96w;32w;95w;243w]) gas_test_call =
  SOME [28998]
Proof
  CONV_TAC cv_eval
QED

Theorem concrete_selected_pc_excludes_other_gas:
  source_gas_evidence [2]
    (gas_test_machine [90w;80w;90w;0w]) gas_test_call = SOME [28994]
Proof
  CONV_TAC cv_eval
QED

Theorem source_returns_concrete_gas_observation:
  ISL (SND (run_trace [(32w,(gas_test_selectors,[0]))]
    (gas_test_machine [90w;95w;82w;96w;32w;95w;243w])
    (Call gas_test_call)))
Proof
  CONV_TAC cv_eval
QED

(* Neither a successful descendant GAS nor a failed distinguished-frame step
   may supply a reading, even when its instruction PC is selected. *)
Theorem selected_gas_frame_isolation:
  LENGTH s.contexts <> d \/ LENGTH s'.contexts <> d \/ ISR r ==>
  selected_gas_step d pcs s (r,s') = NONE
Proof
  Cases_on `r` >> simp[selected_gas_step_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem exhausted_evidence_is_not_an_expected_revert:
  SND (run_trace [(32w,(gas_test_selectors,[]))]
    (gas_test_machine [90w;0w])
    (Call (gas_test_call with expectedOutput := NONE))) =
  INR (Error (RuntimeError "source gas evidence consumption failed"))
Proof
  CONV_TAC cv_eval
QED

Theorem leftover_evidence_is_not_an_expected_revert:
  SND (run_trace [(32w,(gas_test_selectors,[0;2]))]
    (gas_test_machine [90w;80w;90w;0w])
    (Call (gas_test_call with expectedOutput := NONE))) =
  INR (Error (RuntimeError "source gas evidence consumption failed"))
Proof
  CONV_TAC cv_eval
QED

Theorem unavailable_execution_is_not_an_expected_revert:
  SND (run_trace [(32w,(gas_test_selectors,[0]))]
    (gas_test_machine [90w;0w])
    (Call (gas_test_call with <| gasLimit := 0; expectedOutput := NONE |>))) =
  INR (Error (RuntimeError "source gas evidence production failed"))
Proof
  CONV_TAC cv_eval
QED

Definition gas_test_deployment_def:
  gas_test_deployment =
    <| sourceAst := [(NONE,
         [FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
           [Assert
             (Builtin (BaseT BoolT) (Bop Eq)
               [Builtin (BaseT (UintT 256)) (Env MsgGas) [];
                Literal (BaseT (UintT 256)) (IntL 46916)]) AssertBare]])];
       sourceExports := []; importMap := []; contractAbi := [];
       deployedAddress := callee_from_tx_to 33w 0 NONE; deployer := 33w;
       deploymentSuccess := T; value := 0; timeStamp := 1; blockNumber := 1;
       blockHashes := []; blobHashes := []; blobBaseFee := 1; gasPrice := 0;
       chainId := 1; callData := []; runtimeBytecode := [];
       storageLayout := <| storage := []; transient := []; code := [] |>;
       sourceGasPcs := []; sourceGasInitPcs := [0];
       initcode := [90w;80w;95w;95w;243w];
       gasLimit := 100000; blockGasLimit := 10000000000; isBlueprint := F |>
End

val () = cv_auto_trans gas_test_deployment_def;

(* Creation additionally charges CREATE and EIP-3860 initcode-word costs. *)
Theorem concrete_constructor_gas_observation:
  deployment_gas_evidence initial_machine_state gas_test_deployment = SOME [46916]
Proof
  CONV_TAC cv_eval
QED

Theorem constructor_consumes_concrete_gas_observation:
  ISL (SND (run_deployment initial_machine_state gas_test_deployment))
Proof
  CONV_TAC cv_eval
QED

Theorem constructor_exhaustion_is_not_an_expected_failed_deployment:
  SND (run_trace [] initial_machine_state
    (Deployment (gas_test_deployment with
      <| sourceGasInitPcs := []; deploymentSuccess := F |>))) =
  INR (Error (RuntimeError "gas observations exhausted"))
Proof
  CONV_TAC cv_eval
QED

(* The callee's GAS at PC 0 must not leak into the caller's selected sites.
   The caller's unselected GAS at PC 7 is the default forwarding operand. *)
Theorem concrete_descendant_gas_is_frame_local:
  source_gas_evidence [0;9]
    ((gas_test_machine [95w;95w;95w;95w;95w;96w;34w;90w;241w;90w;0w])
      with accounts updated_by
        update_account 34w (empty_account_state with code := [90w;0w]))
    gas_test_call = SOME [26381]
Proof
  CONV_TAC cv_eval
QED

Theorem constructor_producer_failure_is_not_an_expected_failed_deployment:
  SND (run_trace [] initial_machine_state
    (Deployment (gas_test_deployment with
      <| gasLimit := 0; deploymentSuccess := F |>))) =
  INR (Error (RuntimeError "source gas evidence production failed"))
Proof
  CONV_TAC cv_eval
QED

(* The exporter records the ABI argument suffix both in initcode and in
   callData. It is transaction input exactly once, including intrinsic cost. *)
Theorem constructor_argument_suffix_is_charged_once:
  deployment_gas_evidence initial_machine_state
    (gas_test_deployment with
      <| initcode := [90w;80w;95w;95w;243w] ++ REPLICATE 31 0w ++ [7w];
         callData := REPLICATE 31 0w ++ [7w] |>) = SOME [46774]
Proof
  CONV_TAC cv_eval
QED

(* The pinned Prague backend defaults to 10**10 transaction gas. The later
   2**24 transaction admission cap must not reject or clamp that evidence. *)
Theorem prague_high_limit_runtime_observation:
  source_gas_evidence [0]
    (gas_test_machine [90w;95w;82w;96w;32w;95w;243w])
    (gas_test_call with gasLimit := 10000000000) = SOME [9999978998]
Proof
  CONV_TAC cv_eval
QED

Theorem prague_high_limit_constructor_observation:
  deployment_gas_evidence initial_machine_state
    (gas_test_deployment with gasLimit := 10000000000) = SOME [9999946916]
Proof
  CONV_TAC cv_eval
QED
