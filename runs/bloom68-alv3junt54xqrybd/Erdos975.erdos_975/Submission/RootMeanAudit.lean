import Submission.RootMean

/-!
# Axiom audit for the original eight root-mean prerequisites

The command below checks every declaration originating in the eight listed
prerequisite modules, including generated helper declarations. It rejects any
axiom other than `propext`, `Classical.choice`, and `Quot.sound`. The broader
`RootMeanGeneralAudit` audits the complete general root-mean import graph.
Neither audit creates axioms or imports the specification.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  if env.header.moduleNames.contains `Submission.Spec then
    throwError "RootMean audit must not import Submission.Spec"
  let modules : Array Name := #[
    `Submission.RootMeanBasic,
    `Submission.RootMeanPeriodic,
    `Submission.RootMeanLinear,
    `Submission.RootMeanIdeals,
    `Submission.RootMeanKummer,
    `Submission.RootMeanConvolution,
    `Submission.RootMeanNumberField,
    `Submission.RootMeanModel]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut state : Lean.CollectAxioms.State := {}
  let prefixes : Array Name := #[`Erdos975Support] ++
    modules.map (fun mod ↦ `_private ++ mod)
  let declarations := env.constants.toList.filter (fun (name, _) ↦
    prefixes.any (fun pre ↦ pre.isPrefixOf name))
  for mod in modules do
    let mut modCount := 0
    for (name, _) in declarations do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == mod then
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
      throwError "Forbidden axiom {ax} in RootMean declarations"
  logInfo m!"RootMean axiom audit passed: {count} declarations; used axioms {state.axioms.toList}"

