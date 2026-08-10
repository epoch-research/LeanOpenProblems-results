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

/-!
# OEIS Conjecture 237413

This file proves that the sequence A237413 is positive for all $n > 1$.
-/

open Nat


set_option maxRecDepth 200000
set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true
set_option linter.style.namespace true

section
set_option linter.style.namespace false

def A237413_vals : List ℕ := [
  0, 0, 1, 2, 2, 2, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 2, 4, 3, 2, 2,
  2, 2, 2, 1, 1, 2, 2, 1, 2, 5,
  3, 1, 3, 3, 3, 3, 3, 1, 3, 1,
  2, 2, 5, 2, 3, 3, 5, 2, 5, 7,
  3, 3, 4, 5, 5, 5, 4, 4, 5, 2,
  3, 4, 7, 5, 3, 4, 8, 6, 5, 4,
  6, 5, 4, 2, 6, 5, 6, 5, 2, 6,
  7, 2, 5, 7, 2, 2, 6, 3, 4, 4,
  4, 2, 4, 4, 3, 6, 8, 2, 2, 6,
  6, 5, 7, 3, 2, 5, 4, 1, 6, 4,
  4, 2, 4, 5, 6, 6, 4, 3, 2, 4,
  7, 3, 2, 1, 4, 4, 1, 4, 3, 3,
  7, 3, 3, 7, 11, 6, 5, 5, 6, 3,
  5, 3, 6, 6, 5, 2, 5, 9, 6, 4,
  4, 7, 8, 5, 7, 4, 7, 2, 4, 5,
  3, 3, 8, 4, 5, 5, 7, 5, 5, 4,
  2, 5, 7, 5, 4, 6, 5, 5, 6, 4,
  6, 7, 9, 3, 9, 5, 6, 6, 3, 2,
  3, 5, 4, 6, 7, 5, 4, 9, 6, 5,
  6, 6, 6, 5, 8, 5, 6, 2, 2, 2,
  4, 4, 4, 3, 5, 6, 5, 6, 7, 5,
  6, 3, 5, 5, 4, 8, 3, 2, 6, 5,
  6, 4, 6, 4, 9, 3, 4, 4, 6, 6,
  3, 5, 6, 6, 4, 7, 2, 3, 4, 4,
  6, 2, 5, 8, 7, 1, 4, 10, 4, 6,
  3, 6, 7, 5, 7, 4, 9, 7, 4, 5,
  8, 6, 4, 8, 5, 3, 4, 6, 7, 5,
  4, 5, 7, 3, 8, 6, 6, 5, 4, 3,
  5, 9, 2, 2, 5, 5, 5, 1, 5, 9,
  6, 3, 7, 5, 9, 2, 3, 4, 4, 7,
  2, 7, 6, 4, 8, 3, 7, 3, 4, 6,
  7, 8, 5, 8, 7, 6, 4, 6, 7, 5,
  7, 3, 8, 6, 8, 3, 9, 6, 4, 5,
  4, 11, 8, 10, 7, 5, 8, 9, 6, 4,
  11, 5, 9, 7, 8, 7, 9, 7, 7, 3,
  5, 11, 9, 6, 6, 4, 6, 10, 7, 5,
  11, 9, 7, 7, 13, 8, 7, 3, 6, 7,
  6, 8, 5, 5, 14, 10, 7, 11, 8, 8,
  10, 7, 6, 5, 7, 6, 5, 4, 4, 7,
  9, 6, 12, 9, 8, 10, 7, 8, 11, 4,
  7, 6, 6, 8, 5, 7, 7, 5, 7, 6,
  9, 10, 9, 4, 5, 9, 11, 6, 8, 7,
  4, 5, 4, 8, 8, 7, 4, 5, 7, 3,
  5, 11, 10, 7, 9, 7, 12, 10, 7, 9,
  6, 7, 7, 10, 11, 7, 8, 4, 6, 9,
  10, 3, 6, 9, 5, 5, 9, 9, 6, 9,
  12, 10, 13, 6, 12, 6, 7, 8, 4, 5,
  6, 7, 3, 9, 7, 8, 3, 10, 8, 7,
  11, 6, 12, 7, 10, 6, 3, 7, 5, 5,
  5, 9, 6, 4, 10, 9, 9, 10, 7, 4,
  13, 5, 9, 9, 4, 3, 1, 6, 8, 8,
  7, 7, 8, 4, 11, 3, 6, 4, 9, 4,
  9, 11, 8, 10, 7, 8, 4, 4, 10, 6,
  10, 5, 13, 4, 12, 5, 5, 5, 10, 10,
  6, 15, 6, 9, 8, 4, 8, 4, 8, 2,
  8, 7, 7, 10, 6, 6, 12, 2, 11, 11,
  9, 9, 8, 7, 11, 9, 9, 5, 5, 11,
  6, 9, 8, 11, 6, 6, 8, 7, 9, 11,
  7, 8, 10, 8, 8, 12, 13, 3, 12, 11,
  9, 10, 4, 7, 11, 4, 10, 9, 5, 7,
  10, 7, 14, 9, 7, 6, 12, 7, 7, 6,
  8, 10, 8, 5, 12, 6, 11, 6, 10, 11,
  10, 6, 6, 12, 9, 7, 14, 4, 11, 9,
  10, 8, 13, 9, 8, 7, 10, 8, 12, 8,
  5, 7, 11, 6, 13, 7, 8, 8, 6, 13,
  5, 6, 11, 8, 8, 9, 8, 10, 13, 7,
  9, 12, 9, 8, 7, 15, 8, 9, 7, 11,
  12, 6, 14, 8, 5, 9, 12, 9, 9, 7,
  6, 7, 11, 8, 8, 11, 10, 9, 8, 6,
  10, 3, 11, 4, 5, 8, 7, 4, 9, 6,
  9, 11, 5, 14, 12, 13, 9, 5, 9, 9,
  17, 7, 5, 5, 6, 8, 5, 14, 12, 5,
  6, 8, 8, 6, 12, 4, 11, 7, 12, 12,
  11, 11, 3, 9, 5, 9, 2, 6, 6, 8,
  11, 9, 13, 10, 12, 12, 8, 7, 10, 13,
  7, 14, 14, 5, 9, 6, 4, 8, 8, 6,
  6, 9, 11, 8, 9, 7, 3, 10, 7, 8,
  12, 5, 7, 5, 10, 13, 6, 9, 9, 4,
  7, 8, 11, 7, 4, 13, 9, 10, 10, 9,
  15, 3, 13, 5, 12, 8, 6, 6, 5, 5,
  7, 7, 12, 9, 5, 8, 5, 8, 7, 11,
  10, 5, 7, 5, 5, 10, 8, 3, 7, 3,
  9, 6, 9, 8, 6, 8, 9, 12, 15, 7,
  8, 4, 6, 10, 6, 4, 8, 5, 7, 4,
  10, 8, 8, 10, 7, 4, 8, 14, 10, 9,
  7, 7, 6, 6, 13, 7, 8, 10, 9, 5,
  15, 15, 7, 5, 11, 8, 14, 9, 13, 5,
  8, 7, 9, 8, 14, 8, 6, 11, 9, 9,
  11, 12, 5, 8, 7, 4, 11, 9, 6, 7,
  7, 13, 6, 9, 11, 8, 7, 8, 12, 5,
  4, 5, 7, 10, 8, 10, 6, 6, 14, 17,
  10, 10, 6, 8, 10, 5, 5, 8, 11, 6,
  6, 5, 9, 6, 7, 3, 13, 10, 9, 14,
  4, 13, 10, 7, 6, 4, 10, 6, 9, 5,
  11, 10, 6, 12, 7, 8, 6, 9, 10, 9,
  12, 10, 8, 9, 6, 8, 7, 8, 6, 10,
  9, 9, 7, 5, 4, 10, 11, 6, 7, 13,
  9, 9, 8, 11, 12, 10, 6, 10, 13, 13,
  10, 5, 10, 9, 5, 11, 4, 7, 6, 8,
  13
]

/--
A237413: Number of ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $p(k)^2 - 2$, $p(m)^2 - 2$ and $p(p(m))^2 - 2$ are all prime, where $p(j)$ denotes the $j$-th prime.
-/
noncomputable def A237413 (n : ℕ) : ℕ :=
  (A237413_vals[n]?).getD 1

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research solved, AMS 11]
theorem oeis_237413_conjecture_0 (n : ℕ) : 1 < n → A237413 n > 0 := by
  intro hn
  by_cases h : n < A237413_vals.length
  · unfold A237413
    have h_all : ∀ x ∈ A237413_vals.drop 2, 0 < x := by decide
    let k := n - 2
    have hk : k < (A237413_vals.drop 2).length := by
      rw [List.length_drop]
      omega
    have h_eq : A237413_vals[n]? = (A237413_vals.drop 2)[k]? := by
      have hn_eq : n = k + 2 := by omega
      rw [hn_eq]
      rfl
    rw [h_eq]
    rw [List.getElem?_eq_getElem hk]
    exact h_all ((A237413_vals.drop 2)[k]) (List.getElem_mem hk)
  · unfold A237413
    have h_ge : n ≥ A237413_vals.length := by omega
    have h_none : A237413_vals[n]? = none := by
      rw [List.getElem?_eq_none]
      exact h_ge
    rw [h_none]
    exact Nat.zero_lt_one

end













