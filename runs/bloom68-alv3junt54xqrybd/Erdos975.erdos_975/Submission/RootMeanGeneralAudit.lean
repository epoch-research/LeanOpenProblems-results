/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.RootMeanGeneralRegression

/-!
# Exhaustive axiom and dependency audit for the general root-mean theorem

Audit EVERY declaration in every imported `Submission` proof module, including
private and generated declarations, the general theorem, and its regression
callers. Recursively collected dependencies may use only `propext`,
`Classical.choice`, and `Quot.sound`. Both a specification import and dependence
on the original Erdős theorem are rejected. This command adds no mathematical
axiom or theorem. The actual Spec compatibility check is kept outside this
import graph, in a temporary verification file.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  if moduleNames.contains `Submission.Spec then
    throwError "RootMeanGeneral audit must not import Submission.Spec"
  unless moduleNames.contains `Submission.RootMeanGeneral do
    throwError "RootMeanGeneral audit did not import the theorem module"
  unless moduleNames.contains `Submission.RootMeanGeneralRegression do
    throwError "RootMeanGeneral audit did not import the regression module"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut moduleCount : Nat := 0
  let mut state : Lean.CollectAxioms.State := {}
  for idx in [:moduleNames.size] do
    let mod := moduleNames[idx]!
    if (`Submission).isPrefixOf mod then
      let declarations := env.header.moduleData[idx]!.constNames
      if declarations.isEmpty then
        throwError "Audit found no declarations from {mod}"
      for name in declarations do
        let (_, nextState) := ((Lean.CollectAxioms.collect name).run env).run state
        state := nextState
      count := count + declarations.size
      moduleCount := moduleCount + 1
      logInfo m!"Audited {declarations.size} declarations from {mod}"
  if state.visited.contains `Erdos975.erdos_975 ||
      state.visited.contains `Erdos975.erdos_975.disproof then
    throwError "Forbidden dependency on the original Erdős theorem"
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Forbidden axiom {ax} in the general root-mean import graph"
  logInfo m!"RootMeanGeneral exhaustive audit passed: {count} declarations in {moduleCount} modules; used axioms {state.axioms.toList}"
