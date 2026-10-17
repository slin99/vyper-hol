# Continue the JSON-facing MLton fuzzing runner

Work on branch `fuzzing`, based on `main` at `79dfbe70274a7395c9170fb8b28aec007ea45170`.
The user wants to continue on the build server. Local builds were stopped at their request.

## Goal

Finish a standalone MLton executable that consumes existing Vyper exported trace JSON,
keeps CV representations internal, and reuses JSON decoding with HOL kernel replay.
Do not change the semantics of `run_test` or `run_trace`. Do not introduce cheats or
invent values for undefined source operations.

## Changes already committed

- `7bf153ed`: shared portable AST/trace JSON decoders, HOL/native import backends,
  frontend CV extraction, runtime emitter, MLton driver, kernel replay, smoke fixtures.
- `c7e68baa`: executable `tools/demo_run_test.sh` and README usage instructions.

The example is written but has NOT passed end to end. `sh -n tools/demo_run_test.sh`
passed. Its first execution stopped because an earlier holbuild process held the
project lock. That earlier process was subsequently cancelled at the user's request.
Do not describe the executable or demo as verified yet.

## First commands on the build server

Ensure `holbuild`, MLton, and Python 3 are installed and on PATH; follow AGENTS.md
and the holbuild skill. Use holbuild for HOL feedback, not interactive proof tools.

```sh
./tools/demo_run_test.sh
```

This invokes `python3 tools/emit_run_test.py --smoke`, which builds the emitter and
kernel smoke theory, compiles `tests/.emit/run-test`, and compares exact CV inputs
and results between native execution and kernel replay. The script then demonstrates
file input and a passing deployment/call array through stdin.

The fixture deliberately contains three passes and two failures. The runner should
print one JSON object per case and exit 1 for that entire fixture. The demo explicitly
handles that expected failure, then expects its stdin example to pass and exits 0.

## Verification observed before stopping

These targets built successfully, without adding cheats:

- `jsonToVyperTypeCVTheory`
- `jsonToVyperExprCVTheory`
- `jsonToVyperCVTheory`
- `vyperTestLibTestTheory`
- `vyperTestEmitSmokeTheory`

Kernel replay of `tests/fixtures/run_test_json/basic.json` produced:

- `test_basic_code`: `INL ()`
- `test_output_mismatch`: `INR (Error (RuntimeError "output mismatch"))`
- `test_expected_revert`: `INL ()`
- `test_unexpected_revert`: `INR (Error (RuntimeError "bounded_int_op bound"))`
- `test_null_code`: `INL ()`

Portable shared decoder sources were MLton-typechecked earlier. The COMPLETE
emitted executable has NOT been compiled or run. Old ignored generated files in
`tests/.emit` must not be mistaken for a successful current build.

## Immediate emitter issue / interrupted build

A completed emitter attempt failed when `cv_eqs_for` encountered the non-CV type
witness `(:8)` in this generated equation:

```sml
cv_hex_pair_to_word8 cv_hi cv_lo =
  cv_mod (cv_add (cv_mul (cv_UNHEX cv_hi) (cv$Num 16)) (cv_UNHEX cv_lo))
    (cv$Num (2 ** dimindex (:8)))
```

The committed `tests/vyperTestEmitScript.sml` now contains `normalize_cv_literals`.
It kernel-normalizes closed nonliteral payloads of `cv$Num`, saves the resulting
equations, and registers them with DefnBase before collecting the CV closure.
A build with this fix was still running when cancelled; its success is UNCONFIRMED.
Investigate its actual output rather than assuming this fix worked or that the old
failure log describes the updated code. Avoid concurrent holbuild processes: they
share a project lock. Do not use `--skip-goalfrag`.

## Architecture and important files

- `frontend/jsonImportTerm.sml`: portable backend signature (intentionally `.sml`;
  HOL dependency loading of a signature-only `.sig` did not produce a loadable `.uo`).
- `frontend/JsonASTDecodeFn.sml`: shared AST decoder, reused by HOL and native code.
- `frontend/JsonImportHol.sml`, `frontend/jsonASTLib.sml`: HOL implementation/wrapper.
- `tests/JsonTraceDecodeFn.sml`, `tests/vyperTestLib.sml`: shared trace/ABI decoding
  and existing HOL API wrapper. Supports exporter objects and root trace arrays.
- `frontend/jsonToVyperCVLib.sml`: registers matching first-order source induction
  principles for CV extraction, including fixed-parameter primitive recursions.
- `frontend/jsonToVyper{Type,Expr,}CVScript.sml`: frontend CV translation theories.
- `tests/vyperTestEmitScript.sml`: emits runtime and HOL-derived constructor/record
  encoders, normalizes lazy CV conditionals to native SML conditionals, assigns
  distinct SML function names, and copies portable HOL JSON sources.
- `tests/emit/numRuntime.sml`: `numML` runtime backed by IntInf natural numbers.
- `tests/emit/JsonImportCV.sml`: symbolic native import terms and CV encoding.
- `tests/emit/runTestMain.sml`, `tests/emit/run-test.mlb`: CLI and MLton build input.
- `tests/vyperJsonReplayLib.{sig,sml}`: prepares the same JSON for closed,
  kernel-checked `run_test` conversions; handles word-literal CV representations.
- `tests/vyperTestEmitSmokeScript.sml`: kernel results and exact input/result golden
  encodings in ignored `tests/.emit/json-smoke.expected`.
- `tools/emit_run_test.py`: emission, MLton compilation, optional parity smoke.
- `tools/demo_run_test.sh`: build/parity plus file and stdin demonstration.

## Invariants and lessons

- Source `interface_constructor_result _ []` reaches undefined `HD []`.
  Keep frontend defined-input conditions (`cv_auto_trans_pre`); do not invent a
  default. The shared decoder rejects empty interface-constructor calls. Runtime
  `run_test` extraction remains unchanged. Do not claim unconditional end-to-end
  JSON/compiler correctness or that native execution itself is a kernel proof.
- Constructor and record encodings are generated from HOL CV representation
  theorems; never guess record field layout or constructor tags.
- Byte import must match HOL `hex_to_rev_bytes`, including odd final nibbles and
  UNHEX's zero fallback. The mismatch fixture intentionally uses odd hex `0001f`.
- Do not globally eta-reduce recursive source equations: that destroys case-branch
  lambdas needed by CV extraction. Use explicit-lambda MAP helpers and
  PURE_REWRITE_RULE to retain boolean equations. The MAP bridge proofs use explicit
  ETA_CONV because simplification with ETA_AX did not close them.
- Recursive expression extraction needed CV output-size bounds for `find_keyword`
  and `call_pop_index`. Those proofs and the custom termination tactic now build.
- The emitter rewrites `cv_if` to lazy native `if`; emitting it as an eager SML
  function would evaluate both branches and break semantics/termination.

## Finish criteria

1. Build the current emitter successfully and resolve actual generation errors.
2. Compile with MLton and run `./tools/demo_run_test.sh` successfully.
3. Observe exact native/kernel parity for all five deployment/call cases, then
   exercise error handling as practical. Do not substitute a mock executable.
4. Keep README and the demo accurate; remove diagnostic scaffolding if introduced.
5. Commit and push the completed work to `fuzzing`. Report only observed verification.

## Push/authentication context

`origin` is HTTPS `https://github.com/verifereum/vyper-hol`; noninteractive HTTPS
credentials were unavailable. A direct SSH push there was denied for `slin99`.
The configured `own` remote is `git@github.com:slin99/vyper-hol.git`; the handoff
is being pushed to its `fuzzing` branch instead. Check the push result.
