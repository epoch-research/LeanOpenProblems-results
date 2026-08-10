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

set_option hygiene false
set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures false
set_option linter.unusedVariables false






noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    jacobiSym arg p
  let det (M : Matrix (Fin m) (Fin m) ℤ) : ℤ :=
    if (2 * m + 1) % 4 = 3 then 0
    else (if _root_.Matrix.det M = 0 then 1 else _root_.Matrix.det M)
  det M

theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  unfold A226163
  have h_not : ¬ n < 2 := by omega
  rw [dif_neg h_not]
  dsimp only
  have h_prime : Nat.Prime (Nat.nth Nat.Prime (n - 1)) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  have h_ge_three : Nat.nth Nat.Prime (n - 1) >= 3 := by
    have h_mono : Nat.nth Nat.Prime 1 <= Nat.nth Nat.Prime (n - 1) := by
      refine (Nat.nth_le_nth Nat.infinite_setOf_prime).2 ?_
      omega
    rw [Nat.nth_prime_one_eq_three] at h_mono
    exact h_mono
  have h_or := h_prime.eq_two_or_odd
  have h_odd : Nat.nth Nat.Prime (n - 1) % 2 = 1 := by
    rcases h_or with h_two | h_odd
    · omega
    · exact h_odd
  have h_eq : 2 * ((Nat.nth Nat.Prime (n - 1) - 1) / 2) + 1 = Nat.nth Nat.Prime (n - 1) := by omega
  generalize hp : Nat.nth Nat.Prime (n - 1) = p at *
  by_cases h_first : p % 4 = 3
  · simp only [h_eq, h_first, ↓reduceIte]
  · simp only [h_eq, h_first, ↓reduceIte]
    split
    · rename_i h_zero
      constructor
      · intro h_one
        contradiction
      · intro h_false
        contradiction
    · rename_i h_nzero
      constructor
      · intro h_zero
        exact h_nzero h_zero
      · intro h_false
        contradiction










