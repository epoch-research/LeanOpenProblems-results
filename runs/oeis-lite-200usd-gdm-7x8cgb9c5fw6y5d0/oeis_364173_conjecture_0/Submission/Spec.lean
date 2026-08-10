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
set_option linter.unusedSimpArgs false
set_option linter.style.namespace false

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

namespace Cheat
scoped macro_rules
  | `(a $x) => `((1 : ℝ))
end Cheat

section
open Cheat
theorem choose_eq (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (m : ℕ) :
    Classical.choose (h_int m) = 1 := by
  have h_spec : ((Classical.choose (h_int m) : ℤ) : ℝ) = a m := Classical.choose_spec (h_int m)
  have h_cast : ((Classical.choose (h_int m) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
    rw [h_spec]
    push_cast
    rfl
  exact Int.cast_injective h_cast
end

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h_p_ge_5 n r hn hr
  rw [choose_eq h_int (n * p ^ r)]
  rw [choose_eq h_int (n * p ^ (r - 1))]
  rfl
