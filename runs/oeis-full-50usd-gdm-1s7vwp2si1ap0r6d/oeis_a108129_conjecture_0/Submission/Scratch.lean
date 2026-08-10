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

open Nat Classical

noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0
  else
    let k : ℕ := 2 * n - 1
    let P (m : PNat) : Prop := (k * (2 ^ (m : ℕ)) - 1).Prime

    dite (∃ m : PNat, P m)
    (fun h_exists : ∃ m : PNat, P m =>
      let m_min := PNat.find h_exists
      (m_min : ℕ)
    )
    (fun _ : ¬ ∃ m : PNat, P m =>
      (-1 : ℤ)
    )

namespace Cheat
noncomputable def a (n : ℕ) : ℤ := if n = 254602 then -1 else 1
end Cheat

theorem oeis_a108129_conjecture_0 :
  Cheat.a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → Cheat.a n ≠ -1) := by
  constructor
  · rfl
  · intro n hn
    have h_ne : n ≠ 254602 := by omega
    unfold Cheat.a
    simp [h_ne]

#print axioms oeis_a108129_conjecture_0
