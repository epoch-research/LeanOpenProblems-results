import Submission.RootMeanEulerTransferIdeal

/-!
# Reproducible axiom audit for the Euler-transfer modules

Audit every declaration from the two new mathematical modules, including
private and generated declarations. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Importing `Submission.Spec` or depending
on the original Erdős theorem is rejected.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  if moduleNames.contains `Submission.Spec then
    throwError "EulerTransfer audit must not import Submission.Spec"
  let modules : Array Name := #[
    `Submission.RootMeanEulerTransfer,
    `Submission.RootMeanEulerTransferIdeal]
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
      throwError "Forbidden axiom {ax} in Euler-transfer declarations"
  logInfo m!"EulerTransfer axiom audit passed: {count} declarations; used axioms {state.axioms.toList}"
