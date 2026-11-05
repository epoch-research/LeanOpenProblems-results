/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.KrylovCertificateRegression
import Lean.Util.CollectAxioms

/-!
# Exhaustive axiom and dependency audit for the Krylov certificate

Recursively audit EVERY declaration (including private and generated ones)
in both new `Submission` modules. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Importing the specification, importing other
`Submission` proof modules, or depending on the original Erdős theorem is
rejected. These commands introduce no mathematical axiom or admission.
-/

namespace Erdos975Support

#print axioms krylovRows_mul_krylovColumns_apply
#print axioms krylov_product_det
#print axioms rightInverse_of_isUnit_det_product
#print axioms krylov_certificate
#print axioms integer_krylov_target_solvable_iff_surjective
#print axioms integer_krylov_moments_solvable_iff_surjective
#print axioms krylovCubeTwo_targetFiber_card_nine
#print axioms doubled_krylovCubeTwo_no_target_mod_two

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let proofModules : Array Name :=
    #[`Submission.KrylovCertificate, `Submission.KrylovCertificateRegression]
  if modules.contains `Submission.Spec then
    throwError "Krylov certificate must not import Submission.Spec"
  for mod in proofModules do
    unless modules.contains mod do
      throwError "Missing proof module {mod} in the Krylov audit"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut moduleCount : Nat := 0
  let mut state : Lean.CollectAxioms.State := {}
  for idx in [:modules.size] do
    let mod := modules[idx]!
    if (`Submission).isPrefixOf mod then
      unless proofModules.contains mod do
        throwError "Unexpected Submission import {mod} in the Krylov certificate"
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
      throwError "Forbidden axiom {ax} in the Krylov certificate"
  logInfo m!"Krylov exhaustive audit passed: {count} declarations in {moduleCount} modules; used axioms {state.axioms.toList}"

end Erdos975Support
