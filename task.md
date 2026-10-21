# Issue #98: source gas observations — checkpoint

## Status

User requested an immediate checkpoint, not completion of the remaining proof work.
All active workers/builds were stopped before committing. This is unfinished integration work, not a verified release.

- Checkpoint branch: `issue-98-gas-observations-checkpoint`.
- Implementation branch before checkpoint: `issue-98-frame-gas-observations`.
- Started from the user's clean `create_blueprint` branch; preserve its blueprint/delegate/custom work.
- Scope: source `msg.gas` / `msg.mana` observations and concrete replay evidence, including constructors.
- Outside this slice: explicit `gas=` forwarding, gas-dependent out-of-gas semantics, and general gas-sensitive compiler correctness. Compiler-supported expressions still exclude `MsgGas`.

## Implemented contract

`evaluation_state.gas_observations : num list` is frame-local evaluation evidence, not persistent account state.

- `observe_msg_gas` consumes one head, checks `< 2 ** 256`, returns `IntV`, or raises an explicit `RuntimeError`.
- Exhaustion does not fabricate a value. An out-of-range head is consumed before failure.
- Shared stateful `eval_builtin` handles the gas read; pure `evaluate_builtin` remains unchanged.
- Recursive and CPS interpreters dispatch through the shared helper.
- Internal calls/defaults thread the list; external callees run through Verifereum, independently of the source list.
- Both frontend spellings map to `Env MsgGas`.
- `pure_expr` excludes gas reads. Source typing accepts them; affected typing/frame/preservation proofs have been migrated but are not all verified.

Public API cutover, with no old-signature shims:

```text
call_external_function orc gs am ... -> (result, machine, requests, remaining_gs)
call_external orc gs am tx -> (result, machine, requests, remaining_gs)
call_external_transaction orc gs am tx -> (result, machine, requests, remaining_gs)
load_contract orc gs am tx mods exps -> (old_sum_result, remaining_gs)
evaluate_defaults cx am gs expressions -> (old_sum_result, remaining_gs)
initial_state am scopes                 # unchanged two-argument API, empty evidence
```

Evidence remains consumed when machine changes roll back. Constants remain evidence-free. Ordinary callers/compiler relations pass `[]` and use the new result shape.

## Concrete replay

Relevant new files:

- `tests/vyperGasObserverScript.sml`: selected-frame, selected-PC observer; captures successful post-`GAS` stack values.
- `tests/vyperPragueTransactionScript.sml`: pinned-exporter transaction entry, reusing Verifereum components without the later EIP-7825 `2 ** 24` transaction-gas admission cap. Recorded limits, other admission checks, fees, nonce updates, access warming, intrinsic charging and creation effects are retained. In-cap agreement theorems connect this entry to Verifereum's entry.
- `tests/vyperGasReplayTestScript.sml`: behavioral boundary regressions, included in `holproject.toml` roots.
- `tools/enrich_gas_metadata.py`: pinned compiler AST/source-map provenance and exact bytecode validation.

Runner changes use the original pre-transaction accounts for evidence execution; concrete effects are not committed before source replay. Runtime and constructor PC sets are separate. Source reads exclude compiler-generated forwarding `GAS` instructions. Exported constructor `initcode` already includes its separately recorded `calldata`; evidence charges this combined byte sequence once.

Decoder/source exclusions now admit `msg.gas` and `msg.mana`, but retain explicit `gas=` exclusion. Replay rejects evidence production failure, exhaustion, invalid values and leftover observations even for expected-failure traces. Transaction gas limit and block gas limit are separate fields.

CI export setup enriches metadata and uses a versioned cache key. README/live compiler docs describe the API and limitations; historical audit/retirement documents have scope notes rather than rewritten historical receipts.

## Observed passing verification

The following are actual completed checks, not inferred:

1. `vyperStateTheory`, `vyperInterpreterTheory`, `jsonToVyperExprTheory`, `vyperGasObserverTheory` built.
2. `vyperSmallStepTheory` built with full CPS equality and defaults CV-precondition proofs. Its nonexistent `evaluate_defaults_ind` reference was replaced by list induction generalizing the evidence list.
3. A throwaway direct HOL source-evaluator smoke passed: one observation consumed, exhaustion rejected, out-of-range head consumed before error. Throwaway files were removed.
4. Pinned compiler metadata enrichment succeeded for the complete local export tree: 6 deployments in 4 files. Constructor probes with and without ABI arguments succeeded. A corrupt runtime-bytecode probe was rejected. A mixed source-read/raw-call probe distinguished source `GAS` sites from compiler forwarding `GAS`.
5. Most recent completed replay build:

```sh
holbuild build --skip-checkpoints --skip-proof-steps \
  vyperGasReplayTestTheory vyperTestLibTestTheory \
  vyperTest_functional_codegen_features_test_gasTheory \
  vyperTest_functional_codegen_features_test_manaTheory \
  vyperTestCoverageReportTheory
```

All targets passed. Each canonical gas/mana file selected 1 test with 3 traces and 0 decode failures; these are nonempty actual replays. The new replay theory proved runtime and constructor observations, frame isolation, strict evidence failures, constructor argument charging once, and exact observations with exporter gas limit `10000000000`.

6. `vyperPragueTransactionTheory` and `vyperOracleEntryTestTheory` built in the preceding command.
7. Prior proof integration reported successful `vyperPureExprTheory` and `vyperEvalPureExprTheory` builds after repairing builtin purity tactics; the resumed workers did not reverify these before checkpoint.

`--skip-proof-steps` disables per-step instrumentation, not kernel proof checking. Do not use `--skip-goalfrag`.

## Remaining work / exact known failures

### Source preservation/type/entry proof integration

Run focused targets, repair actual failures, then build the default roots. No new admissions or weakened statements are acceptable.

```sh
holbuild build --skip-checkpoints --skip-proof-steps \
  vyperTypeBuiltinsTheory vyperPureExprTheory vyperEvalPureExprTheory \
  vyperExprNoControlTheory vyperEvalOutcomeSuffixTheory \
  vyperTypeEvalSoundnessTheory vyperTypeEntryReadinessTheory \
  vyperTypeContractSoundnessTheory vyperTypeEntryDefaultsTheory \
  vyperTypeExternalCallMachineTheory vyperTypeDeploymentMachineTheory \
  vyperTypeSelectedEntryTheory vyperLogPreservationTheory \
  vyperOracleStateTestTheory
```

- Last substantive root log failure: `vyperLogPreservationTheory`, `case_expr_builtin_logs`, `DISCH_THEN` / `FIRST_ASSUM` failure. Use the shared builtin field-preservation lemmas rather than assuming the entire state is unchanged.
- `vyperEvalOutcomeSuffixTheory` last retained root log reached `gas_frame_primitives`; suffix proofs need completed acceptance.
- `vyperExprNoControlTheory` last retained root log reached `int_call_tail_no_control`; acceptance remains incomplete.
- `vyperTypeBuiltinsTheory` and downstream type/entry acceptance remain unverified. The resumed typing worker made no edits and was cancelled before any target completed.
- The resumed entry worker made no edits. Its first isolated build timed out during prerequisite builds; its retry was cancelled. No entry acceptance target from that worker was observed passing.
- The resumed frame worker's build was cancelled. Its cancellation-time error had an empty child-log tail, not a new proof diagnosis. Do not treat it as evidence of a particular theorem failure.

Existing root logs: `.holbuild/logs/current/vyper-hol/<Theory>/build.log`.
Isolated artifact workspaces used by the last workers: `/tmp/vyper-gas-frame-finish`, `/tmp/vyper-gas-typing-finish`, `/tmp/vyper-gas-entry-finish`. Temporary directories may not survive a new session.

For independent builds, create separate artifact directories and run:

```sh
holbuild --source-dir /home/s1nn105/sequent/vyper-hol build \
  --skip-checkpoints --skip-proof-steps TARGET...
```

Artifacts live under the command's cwd. Concurrent builds sharing one artifact root conflict on the project lock.

### Compiler/boundary regression integration

The following command was started but explicitly cancelled for this checkpoint; no aggregate passing result exists:

```sh
holbuild build --skip-checkpoints --skip-proof-steps \
  e2eBoundaryTestTheory e2eSourceBoundaryCVTestTheory \
  loweringBoundaryChecksTheory e2eCompositionChecksTheory \
  e2eDeployChecksTheory evalCompilerRangeTheory
```

### Separate existing assertion encountered

A broader command including `vyperOracleIntegrationTestTheory` failed in `vyperExtCallCpsCVTestTheory` at `cpscv_NONE_concrete_code_failure`: its expected no-code error assertion reduced to `F`. The current concrete `ext_call_precheck_ok` distinguishes return types; inspect the actual contract before changing anything. This test was left untouched. Do not describe it as a proven pre-existing failure on the starting branch: no before-change baseline run established that.

### Tooling

Checkpoint/proof-step instrumentation previously hit invalid checkpoint restores and a holbuild runtime `Thread does not exist` error. These were reported through `xd://report_issue`. Uninstrumented kernel proof builds above were used instead. No LSP servers were configured.

## Resumption discipline

- Do not recreate the branch or discard current edits.
- Read `skill://holbuild` and repository `AGENTS.md`.
- Resume the proof failures before claiming completion; passing concrete gas replays do not imply all affected proofs compile.
- Preserve the user's earlier contract-creation/delegate work and existing unrelated compiler admission scope.
- Do not restart cancelled jobs blindly; inspect the relevant retained log/target and actual available artifacts.
- All parent throwaway source/JSON/HOL probes were removed. No final full-suite or compiler-certification claim has been made.
