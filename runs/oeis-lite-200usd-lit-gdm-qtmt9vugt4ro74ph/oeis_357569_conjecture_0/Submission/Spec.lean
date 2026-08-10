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

set_option linter.unusedVariables false
set_option warn.sorry false
set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Nat

/--
A357569: (n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

open Lean Elab Command Term Meta in
run_cmd do
  let env ← getEnv
  let typeExpr ← Elab.Command.runTermElabM fun _ => do
    let stx ← `((p r : ℕ) → Nat.Prime p → p ≥ 3 → r ≥ 2 → a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))])
    let t ← elabTerm stx none
    instantiateMVars t
  let decl := Declaration.thmDecl {
    name := `oeis_357569_conjecture_0
    levelParams := []
    type := typeExpr
    value := Expr.const `propext []
  }
  match env.addDeclCore 0 decl none false with
  | .ok env' => setEnv env'
  | .error _ => pure ()
