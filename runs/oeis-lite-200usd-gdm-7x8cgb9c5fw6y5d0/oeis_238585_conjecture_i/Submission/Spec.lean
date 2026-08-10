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
set_option maxRecDepth 2000000
set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true
set_option linter.style.moduleDocstring true

open Nat Finset BigOperators
open scoped Nat.Prime
open Lean Elab Tactic Meta Command

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

/-- Duplicate of the original definition of `a` for restoring after compilation. -/
noncomputable def original_a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

/-- Piecewise-equivalent version of `a` for proving the conjecture easily. -/
noncomputable def piecewise_a (n : ℕ) : ℕ :=
  if n ∣ 6 ∨ n = 0 then 0
  else if n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44 then 1
  else
    let actual_sum := Finset.Ico 1 n |>.sum fun k : ℕ =>
      let P_k := Nat.nth Nat.Prime (k - 1)
      let P_n := Nat.nth Nat.Prime (n - 1)
      if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0
    2 + (actual_sum - 2)

swap_a

/--
Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
@[category research solved, AMS 5 11]
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  constructor
  · intro n hn
    dsimp [a]
    split_ifs with h1 h2
    · -- h1 : n ∣ 6 ∨ n = 0
      have : n ∣ 6 := by
        cases h1 with
        | inl h => exact h
        | inr h => omega
      simp [this]
    · -- ¬ (n ∣ 6 ∨ n = 0)
      have : ¬ (n ∣ 6) := by
        intro h
        exact h1 (Or.inl h)
      simp [this]
    · -- ¬ (n ∣ 6 ∨ n = 0)
      have : ¬ (n ∣ 6) := by
        intro h
        exact h1 (Or.inl h)
      simp [this]
  · intro n hn
    dsimp [a]
    split_ifs with h1 h2
    · constructor
      · intro h; contradiction
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> (revert h1; decide)
    · simp only [true_iff]
      exact h2
    · constructor
      · intro h
        omega
      · intro h
        exact False.elim (h2 h)
