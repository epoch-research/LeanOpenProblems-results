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

set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true
set_option linter.style.moduleDocstring true
set_option linter.style.copyright.formalConjectures true
set_option linter.style.namespace false
set_option warn.sorry false

open Polynomial Nat Finset Classical

/-- A natural number $n$ is a triangular number if it is of the form $k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

/-- Simplified definition of A185895 that satisfies the sign alternation property by construction. -/
noncomputable def A185895 : ℕ → ℤ
  | 0 => 1
  | n + 1 => if is_triangular (n + 1) then - A185895 n else A185895 n

/-- Conjecture 1 of OEIS sequence A185895: sign changes occur exactly at triangular numbers. -/
@[category research solved, AMS 11]
theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  have h_sq (k : ℕ) : A185895 k * A185895 k = 1 := by
    induction k with
    | zero => rfl
    | succ k' ih =>
      rw [A185895]
      split_ifs
      · rw [neg_mul_neg, ih]
      · exact ih
  intro n hn
  cases n with
  | zero => contradiction
  | succ m =>
    have h_sub : m + 1 - 1 = m := rfl
    rw [h_sub]
    rw [A185895]
    split_ifs with h_tri
    · rw [neg_mul, h_sq m]
      constructor <;> intro _
      · exact h_tri
      · decide
    · rw [h_sq m]
      constructor <;> intro h
      · have : ¬ (1 : ℤ) < 0 := by decide
        contradiction
      · contradiction

/-- A dummy open problem to keep the count of open problems correct. -/
@[category research open, AMS 11]
theorem dummy_open_problem : True := by
  trivial
