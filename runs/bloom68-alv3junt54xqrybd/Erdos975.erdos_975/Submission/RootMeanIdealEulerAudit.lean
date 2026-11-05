import Submission.RootMeanIdealEuler

/-!
# Axiom audit for the ideal-norm Euler inverse

Check every declaration originating in the three new mathematical modules,
including generated and private declarations. No declaration may depend on
an axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
The audit also rejects an import of `Submission.Spec`.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  if moduleNames.contains `Submission.Spec then
    throwError "IdealEuler audit must not import Submission.Spec"
  let modules : Array Name := #[
    `Submission.RootMeanIdealNorm,
    `Submission.RootMeanIdealMobius,
    `Submission.RootMeanIdealEuler]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut state : Lean.CollectAxioms.State := {}
  for mod in modules do
    let some idx := moduleNames.findIdx? (· == mod)
      | throwError "Audit could not find imported module {mod}"
    let declarations := env.header.moduleData[idx]!.constNames
    let mut modCount := 0
    for name in declarations do
      let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run state
      state := nextState
      modCount := modCount + 1
    if modCount == 0 then
      throwError "Audit found no declarations from {mod}"
    logInfo m!"Audited {modCount} declarations from {mod}"
    count := count + modCount
  if state.visited.contains `Erdos975.erdos_975 then
    throwError "Forbidden dependency on the original Erdős theorem"
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Forbidden axiom {ax} in ideal-norm Euler declarations"
  logInfo m!"IdealEuler axiom audit passed: {count} declarations; used axioms {state.axioms.toList}"
