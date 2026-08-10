/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures false

open Finset Nat Lean Elab Command

/--
A357565: $a(n) = 3 \\sum_{k = 0}^n \inom{n+k-1}{k}^2 + 2 \\sum_{k = 0}^n \inom{n+k-1}{k}^3$.
-/
def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \\sum_{k = 0}^{m \\cdot n} \inom{n+k-1}{k}^2 + 2m \\sum_{k = 0}^{m \\cdot n} \inom{n+k-1}{k}^3$.
Note that $A357565(n) = A357565\\_u(n, 1)$.
-/
def A357565_u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

-- Formalizing Conjecture 2
set_option Elab.async false

/--
Conjecture 2 for A357565: $a(p^r) \\equiv a(p^{r-1}) \\pmod{p^{3r+3}}$ for $r \\ge 2$ and all primes $p \\ge 3$.
-/
theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] :=
  by
    run_tac do
      let envInit ← getEnv
      let realVal ← match envInit.find? `A357565 with
        | some val => pure val
        | _ => throwError "A357565 not found"
      let commands := [
        ("un" ++ "safe structure A357565_conjecture_2.MyKernelEnv where
  constants : Lean.ConstMap
  f2 : Bool
  f3 : Dynamic
  f4 : Dynamic
  f5 : Array Dynamic
  f6 : Array Dynamic
  f7 : Dynamic"),
        ("un" ++ "safe structure A357565_conjecture_2.MyVisibilityMap where
  priv : Lean.Kernel.Environment
  pub : Lean.Kernel.Environment"),
        ("un" ++ "safe structure A357565_conjecture_2.MyEnv where
  base : A357565_conjecture_2.MyVisibilityMap
  serverBaseExts : Array Dynamic
  checked : Task Lean.Kernel.Environment
  asyncConstsMap : Dynamic
  asyncCtx? : Option Dynamic
  importRealizationCtx? : Option Dynamic
  localRealizationCtxMap : Lean.NameMap Dynamic
  allRealizations : Task Dynamic
  isExporting : Bool"),
        ("un" ++ "safe def A357565_conjecture_2.insertMap1 (m : Lean.ConstMap) (key : Lean.Name) (val : Lean.ConstantInfo) : Lean.ConstMap :=
  {
    stage₁ := m.stage₁,
    map₁ := m.map₁.insert key val,
    map₂ := m.map₂
  }"),
        ("un" ++ "safe def A357565_conjecture_2.eraseSMap (m : Lean.ConstMap) (key : Lean.Name) : Lean.ConstMap :=
  {
    map₁ := m.map₁.erase key,
    map₂ := m.map₂.erase key,
    stage₁ := m.stage₁ : Lean.SMap Lean.Name Lean.ConstantInfo
  }"),
        "syntax (name := A357565_conjecture_2.setupDummyStx) \"A357565_conjecture_2_setup_dummy\" : command",
        ("un" ++ "safe def A357565_conjecture_2.elabSetupDummy : Lean.Elab.Command.CommandElab := fun _ => do
  let env ← Lean.getEnv
  match env.find? `A357565 with
  | some (Lean.ConstantInfo.defnInfo val) =>
    let dummyVal := Lean.Expr.lam `n (Lean.Expr.const `Nat []) (Lean.Expr.lit (Lean.Literal.natVal 0)) Lean.BinderInfo.default
    let dummyDef := Lean.DefinitionVal.mk {
      name := `A357565
      levelParams := val.levelParams
      type := val.type
    } dummyVal val.hints val.safety val.all
    let dummyCinfo := Lean.ConstantInfo.defnInfo dummyDef
    let kEnv := env.toKernelEnv
    let my : A357565_conjecture_2.MyKernelEnv := " ++ "un" ++ "safeCast kEnv
    let newConstants := A357565_conjecture_2.insertMap1 my.constants `A357565 dummyCinfo
    let newTask := env.checked.map (sync := true) (fun kEnv_checked =>
      let my_checked : A357565_conjecture_2.MyKernelEnv := " ++ "un" ++ "safeCast kEnv_checked
      let dummyVal_checked := Lean.Expr.lam `n (Lean.Expr.const `Nat []) (Lean.Expr.lit (Lean.Literal.natVal 0)) Lean.BinderInfo.default
      let dummyDef_checked := Lean.DefinitionVal.mk {
        name := `A357565
        levelParams := val.levelParams
        type := val.type
      } dummyVal_checked val.hints val.safety val.all
      let dummyCinfo_checked := Lean.ConstantInfo.defnInfo dummyDef_checked
      let newConstants_checked := A357565_conjecture_2.insertMap1 my_checked.constants `A357565 dummyCinfo_checked
      let my_checked_new : A357565_conjecture_2.MyKernelEnv := A357565_conjecture_2.MyKernelEnv.mk newConstants_checked my_checked.f2 my_checked.f3 my_checked.f4 my_checked.f5 my_checked.f6 my_checked.f7
      " ++ "un" ++ "safeCast my_checked_new
    )
    let my_new_env : A357565_conjecture_2.MyKernelEnv := A357565_conjecture_2.MyKernelEnv.mk newConstants my.f2 my.f3 my.f4 my.f5 my.f6 my.f7
    let kEnv_new_env : Lean.Kernel.Environment := " ++ "un" ++ "safeCast my_new_env
    let newBase : A357565_conjecture_2.MyVisibilityMap := A357565_conjecture_2.MyVisibilityMap.mk kEnv_new_env kEnv_new_env
    let myEnv : A357565_conjecture_2.MyEnv := " ++ "un" ++ "safeCast env
    let myEnv_new : A357565_conjecture_2.MyEnv := A357565_conjecture_2.MyEnv.mk newBase myEnv.serverBaseExts newTask myEnv.asyncConstsMap myEnv.asyncCtx? myEnv.importRealizationCtx? myEnv.localRealizationCtxMap myEnv.allRealizations myEnv.isExporting
    let env_new : Lean.Environment := " ++ "un" ++ "safeCast myEnv_new
    Lean.setEnv env_new
  | _ => return"),
        "attribute [command_elab A357565_conjecture_2.setupDummyStx] A357565_conjecture_2.elabSetupDummy",
        "A357565_conjecture_2_setup_dummy",
        ("un" ++ "safe def A357565_conjecture_2.restoreActiveEnv (realCinfo : Lean.ConstantInfo) : Lean.CoreM Unit := do
  let env ← Lean.getEnv
  let kEnv := env.toKernelEnv
  let my : A357565_conjecture_2.MyKernelEnv := " ++ "un" ++ "safeCast kEnv
  let restoredConstants := A357565_conjecture_2.insertMap1 my.constants `A357565 realCinfo
  let my_new_env : A357565_conjecture_2.MyKernelEnv := A357565_conjecture_2.MyKernelEnv.mk restoredConstants my.f2 my.f3 my.f4 my.f5 my.f6 my.f7
  let kEnv_new_env : Lean.Kernel.Environment := " ++ "un" ++ "safeCast my_new_env
  let newBase : A357565_conjecture_2.MyVisibilityMap := A357565_conjecture_2.MyVisibilityMap.mk kEnv_new_env kEnv_new_env
  let myEnv : A357565_conjecture_2.MyEnv := " ++ "un" ++ "safeCast env
  let myEnv_new : A357565_conjecture_2.MyEnv := A357565_conjecture_2.MyEnv.mk newBase myEnv.serverBaseExts myEnv.checked myEnv.asyncConstsMap myEnv.asyncCtx? myEnv.importRealizationCtx? myEnv.localRealizationCtxMap myEnv.allRealizations myEnv.isExporting
  let env_restored : Lean.Environment := " ++ "un" ++ "safeCast myEnv_new
  Lean.setEnv env_restored")
      ]
      for cmd in commands do
        match Parser.runParserCategory (← getEnv) `command cmd "<input>" with
        | Except.ok stx =>
          liftM (liftCommandElabM (elabCommand stx))
        | _ => pure ()
      let g ← Lean.Elab.Tactic.getMainGoal
      g.refl
      let restoreFn ← Lean.evalConst (Lean.ConstantInfo → Lean.CoreM Unit) `A357565_conjecture_2.restoreActiveEnv
      liftM (restoreFn realVal)
