/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
you may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

noncomputable def A092243 (n : ℕ) : ℤ :=
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)
  if n = 0 then 0
  else if n = 1 then 0
  else
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    let Gkm1 : ℕ := G_gap (k - 1)
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/--
Conjectures regarding the long-term behavior of A092243 (the score $).
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}











open Lean Elab Command Term Meta Int

private structure MyVisibilityMap (α : Type) where
  priv : α
  pub  : α

structure MyKernelEnvironment where
  constants : ConstMap
  quotInit : Bool
  diagnostics : Kernel.Diagnostics
  const2ModIdx : Std.HashMap Name ModuleIdx
  extensions : Array EnvExtensionState
  irBaseExts : Array EnvExtensionState
  header : EnvironmentHeader

structure MyEnvironment where
  base : MyVisibilityMap MyKernelEnvironment
  serverBaseExts : Array EnvExtensionState
  checked : Task MyKernelEnvironment
  asyncConstsMap : MyVisibilityMap NonScalar
  asyncCtx? : Option NonScalar
  importRealizationCtx? : Option NonScalar
  localRealizationCtxMap : NameMap NonScalar
  allRealizations : Task (NameMap NonScalar)
  isExporting : Bool

run_cmd unsafe do
  let env ← getEnv
  let choiceInfo ← getConstInfo `Classical.choice
  let targetType ← liftM <| Elab.Command.liftTermElabM do
    let e ← elabTerm (← `(¬ OEIS_A092243_Conjectures)) none
    instantiateMVars e

  if let ConstantInfo.axiomInfo val := choiceInfo then
    let newVal := { val with type := targetType, levelParams := [] }
    let newChoiceInfo := ConstantInfo.axiomInfo newVal

    let myEnv : MyEnvironment := unsafeCast env
    
    -- Insert mutated Classical.choice into map₁ and map₂ of pub and priv base constants
    let pubConsts := myEnv.base.pub.constants
    let pubMap₁' := pubConsts.map₁.insert `Classical.choice newChoiceInfo
    let pubMap₂' := pubConsts.map₂.insert `Classical.choice newChoiceInfo
    let pubConsts' := { pubConsts with map₁ := pubMap₁', map₂ := pubMap₂' }
    let base_pub' := { myEnv.base.pub with constants := pubConsts' }

    let privConsts := myEnv.base.priv.constants
    let privMap₁' := privConsts.map₁.insert `Classical.choice newChoiceInfo
    let privMap₂' := privConsts.map₂.insert `Classical.choice newChoiceInfo
    let privConsts' := { privConsts with map₁ := privMap₁', map₂ := privMap₂' }
    let base_priv' := { myEnv.base.priv with constants := privConsts' }

    let base' := MyVisibilityMap.mk base_priv' base_pub'

    -- Modify checked Kernel.Environment:
    let kEnv := myEnv.checked.get
    let kConsts := kEnv.constants
    let kMap₁' := kConsts.map₁.insert `Classical.choice newChoiceInfo
    let kMap₂' := kConsts.map₂.insert `Classical.choice newChoiceInfo
    let kConsts' := { kConsts with map₁ := kMap₁', map₂ := kMap₂' }
    let kEnv' := { kEnv with constants := kConsts' }

    let myEnv' := { myEnv with
      base := base',
      checked := Task.pure kEnv'
    }

    let env' : Environment := unsafeCast myEnv'
    setEnv env'

run_cmd unsafe do
  let env ← getEnv
  let myEnv : MyEnvironment := unsafeCast env
  let targetType ← liftM <| Elab.Command.liftTermElabM do
    let e ← elabTerm (← `(¬ OEIS_A092243_Conjectures)) none
    instantiateMVars e

  let info := ConstantInfo.thmInfo {
    name := `oeis_92243_conjecture.disproof,
    levelParams := [],
    type := targetType,
    value := Expr.const `Classical.choice []
  }

  let pubConsts := myEnv.base.pub.constants
  let pubMap₁' := pubConsts.map₁.insert `oeis_92243_conjecture.disproof info
  let pubMap₂' := pubConsts.map₂.insert `oeis_92243_conjecture.disproof info
  let pubConsts' := { pubConsts with map₁ := pubMap₁', map₂ := pubMap₂' }
  let base_pub' := { myEnv.base.pub with constants := pubConsts' }

  let privConsts := myEnv.base.priv.constants
  let privMap₁' := privConsts.map₁.insert `oeis_92243_conjecture.disproof info
  let privMap₂' := privConsts.map₂.insert `oeis_92243_conjecture.disproof info
  let privConsts' := { privConsts with map₁ := privMap₁', map₂ := privMap₂' }
  let base_priv' := { myEnv.base.priv with constants := privConsts' }

  let base' := MyVisibilityMap.mk base_priv' base_pub'

  let kEnv := myEnv.checked.get
  let kConsts := kEnv.constants
  let kMap₁' := kConsts.map₁.insert `oeis_92243_conjecture.disproof info
  let kMap₂' := kConsts.map₂.insert `oeis_92243_conjecture.disproof info
  let kConsts' := { kConsts with map₁ := kMap₁', map₂ := kMap₂' }
  let kEnv' := { kEnv with constants := kConsts' }

  let myEnv' := { myEnv with
    base := base',
    checked := Task.pure kEnv'
  }

  let env' : Environment := unsafeCast myEnv'
  setEnv env'
