Theory vyperPragueTransaction
Ancestors
  vfmCompute vfmContext vfmExecution vfmState vfmTypes
  arithmetic list option pair finite_map
Libs
  cv_transLib

(* The pinned export backend targets Prague. Verifereum's transaction entry
   additionally imposes the later EIP-7825 2**24 transaction gas cap. Replay
   retains the exported gas limit without that later-fork admission check.
   All other admission checks, fees, nonce updates, access warming, intrinsic
   charging, authorization processing and creation effects are unchanged. *)
Definition prague_pre_transaction_updates_def:
  prague_pre_transaction_updates a blobBaseFee t =
  if (case t.maxFeePerBlobGas of SOME mf =>
           mf < blobBaseFee \/ NULL t.blobVersionedHashes
         | _ => F) then NONE else
  if ~EVERY versioned_hash_correct t.blobVersionedHashes then NONE else
  if IS_NONE t.to /\ LENGTH t.data > 2 * max_code_size then NONE else
  let sender = lookup_account t.from a in
  if sender.balance < max_total_cost t then NONE else
  if ~NULL sender.code /\ ~is_delegation sender.code then NONE else
  let fee = t.gasLimit * t.gasPrice + total_blob_gas t * blobBaseFee in
  if sender.nonce <> t.nonce \/ t.nonce >= 2 ** 64 - 1 then NONE else
  if sender.balance < fee + t.value then NONE else
  let updatedSender = sender with
    <| nonce := SUC sender.nonce; balance := sender.balance - fee |> in
  SOME (update_account t.from updatedSender a)
End

val () = cv_auto_trans prague_pre_transaction_updates_def;

Theorem prague_pre_transaction_updates_agrees:
  t.gasLimit <= 2 ** 24 ==>
  prague_pre_transaction_updates a fee t = pre_transaction_updates a fee t
Proof
  strip_tac >>
  `~(t.gasLimit > 2 ** 24)` by decide_tac >>
  simp[prague_pre_transaction_updates_def, pre_transaction_updates_def]
QED

Definition prague_initial_state_def:
  prague_initial_state dom static chainId prevHashes blk accs tx =
  case prague_pre_transaction_updates
         accs (base_fee_per_blob_gas blk.excessBlobGas) tx
  of NONE => NONE | SOME accounts =>
    let callee = callee_from_tx_to tx.from tx.nonce tx.to in
    let baseAccesses = initial_access_sets blk.coinBase callee tx in
    let (postAuthAccounts, postAuthAccesses, authRefund) =
          process_authorizations chainId tx.authorizationList accounts baseAccesses 0 in
    let (code, accesses) = code_from_tx postAuthAccounts postAuthAccesses tx in
    let rd = if IS_SOME tx.to then empty_return_destination else Code callee in
    let rb = initial_rollback postAuthAccounts accesses in
    let ctxt = initial_context callee code static rd tx in
    let authListLen = LENGTH tx.authorizationList in
    case apply_intrinsic_cost tx.accessList authListLen ctxt of NONE => NONE | SOME ctxt =>
    SOME <| contexts := [(ctxt, rb)];
            txParams := initial_tx_params chainId prevHashes blk tx authRefund;
            rollback := rb; msdomain := dom |>
End

val () = prague_initial_state_def |>
  ONCE_REWRITE_RULE[GSYM lookup_account_def] |>
  ONCE_REWRITE_RULE[GSYM update_account_def] |>
  cv_auto_trans;

Theorem prague_initial_state_agrees:
  tx.gasLimit <= 2 ** 24 ==>
  prague_initial_state d st c h b a tx = initial_state d st c h b a tx
Proof
  strip_tac >> simp[prague_initial_state_def, initial_state_def,
       prague_pre_transaction_updates_agrees]
QED

Definition prague_run_create_def:
  prague_run_create dom static chainId prevHashes blk accounts tx =
  case prague_initial_state dom static chainId prevHashes blk accounts tx of
    NONE => NONE
  | SOME s => SOME $
    let crb = HD s.contexts in
    let ctxt = FST crb in
    let calleeAddress = ctxt.msgParams.callee in
    if IS_SOME tx.to then
      INR (s.rollback.accounts,
           s with rollback updated_by
             (\r. r with accounts updated_by
               transfer_value tx.from calleeAddress tx.value),
           if fIN calleeAddress precompile_addresses
           then SOME calleeAddress else NONE)
    else
      let accounts = s.rollback.accounts in
      let callee = lookup_account calleeAddress accounts in
      if account_already_created callee then
        INL (post_transaction_accounting blk tx (SOME AddressCollision) accounts
              (s with contexts :=
                [(ctxt with gasUsed := ctxt.msgParams.gasLimit, SND crb)]))
      else
        INR (accounts,
          s with <| rollback updated_by (\r. r with accounts updated_by
                     (transfer_value tx.from calleeAddress tx.value o
                      increment_nonce calleeAddress));
                    contexts updated_by
                      (set_last_accounts
                        (update_account calleeAddress empty_account_state
                          (SND crb).accounts)) |>, NONE)
End

val prague_run_create_pre_def = prague_run_create_def
  |> SIMP_RULE std_ss [combinTheory.o_DEF]
  |> cv_auto_trans_pre "prague_run_create_pre";

Theorem prague_run_create_pre[cv_pre]:
  prague_run_create_pre d st c p b a t
Proof
  rw[prague_run_create_pre_def, prague_initial_state_def,
     prague_pre_transaction_updates_def, execution_state_component_equality,
     initial_rollback_def, code_from_tx_def, set_last_accounts_pre_cases] >>
  strip_tac >> gvs[CaseEq"option", UNCURRY]
QED

Theorem prague_run_create_agrees:
  tx.gasLimit <= 2 ** 24 ==>
  prague_run_create d st c h b a tx = run_create d st c h b a tx
Proof
  strip_tac >> simp[prague_run_create_def, run_create_def, prague_initial_state_agrees]
QED
