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

open Nat BigOperators Finset

/--
A208425: Expansion of $\sum_{n\ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$.
The $n$-th term $a(n)$ is given by the known combinatorial identity:
$$ a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k} $$
-/
def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) * ((n - k).choose k) * ((n + k).choose k)

/-- Conjecture: (i) For any prime p > 3 and positive integer n,
the number (a(p*n)-a(n))/(p*n)^3 is always a p-adic integer. -/
lemma padicValRat_ge_zero_of_dvd (p : ℕ) [hp : Fact p.Prime] (a : ℤ) (b : ℤ) (hb : b ≠ 0)
    (h : (p : ℤ) ^ (padicValInt p b) ∣ a) : padicValRat p (a / b : ℚ) ≥ 0 := by
  by_cases ha : a = 0
  · simp [ha]
  · have ha_q : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have hb_q : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    rw [padicValRat.div ha_q hb_q]
    rw [padicValRat.of_int, padicValRat.of_int]
    have h_dvd := (padicValInt_dvd_iff (padicValInt p b) a).mp h
    rcases h_dvd with rfl | h_le
    · contradiction
    · omega

theorem val_pow_three (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n > 0) :
  padicValInt p ((p * n : ℤ) ^ 3) = 3 * (1 + padicValInt p n) := by
  have hp_pos : p ≠ 0 := hp.elim.ne_zero
  have hn_pos : n ≠ 0 := by omega
  have h_pn : p * n ≠ 0 := mul_ne_zero hp_pos hn_pos
  -- Rewrite padicValInt
  rw [padicValInt, padicValInt]
  have h_abs_pow : Int.natAbs ((p * n : ℤ) ^ 3) = (p * n) ^ 3 := by
    rw [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [h_abs_pow]
  rw [padicValNat.pow 3 h_pn]
  rw [padicValNat.mul hp_pos hn_pos]
  rw [padicValNat_self]
  rw [Int.natAbs_natCast]

theorem choose_identity (n k : ℕ) :
  (n.choose k) * ((n - k).choose k) * ((n + k).choose k) =
  ((n + k).choose (3 * k)) * ((3 * k).choose k) * ((2 * k).choose k) := by
  have h_symm : (3 * k).choose k = (3 * k).choose (2 * k) := by
    have h_sub : 3 * k - 2 * k = k := by omega
    have h_le : 2 * k ≤ 3 * k := by omega
    have h_symm_raw := choose_symm h_le
    rw [h_sub] at h_symm_raw
    exact h_symm_raw
  have h_rhs_eq : ((n + k).choose (3 * k)) * ((3 * k).choose k) * ((2 * k).choose k) =
                  ((n + k).choose (3 * k)) * ((3 * k).choose (2 * k)) * ((2 * k).choose k) := by
    rw [h_symm]
  have h_le2 : 2 * k ≤ 3 * k := by omega
  have h_mul1 := choose_mul h_le2 (n := n + k)
  have h_sub2 : n + k - 2 * k = n - k := by omega
  have h_sub3 : 3 * k - 2 * k = k := by omega
  rw [h_sub2, h_sub3] at h_mul1
  have h_rhs_eq2 : ((n + k).choose (3 * k)) * ((3 * k).choose (2 * k)) * ((2 * k).choose k) =
                   ((n + k).choose (2 * k)) * ((n - k).choose k) * ((2 * k).choose k) := by
    rw [h_mul1]
  have h_rhs_eq3 : ((n + k).choose (2 * k)) * ((n - k).choose k) * ((2 * k).choose k) =
                   ((n + k).choose (2 * k)) * ((2 * k).choose k) * ((n - k).choose k) := by
    ring
  have h_le3 : k ≤ 2 * k := by omega
  have h_mul2 := choose_mul h_le3 (n := n + k)
  have h_sub4 : n + k - k = n := by omega
  have h_sub5 : 2 * k - k = k := by omega
  rw [h_sub4, h_sub5] at h_mul2
  have h_rhs_eq4 : ((n + k).choose (2 * k)) * ((2 * k).choose k) * ((n - k).choose k) =
                   ((n + k).choose k) * (n.choose k) * ((n - k).choose k) := by
    rw [h_mul2]
  have h_lhs_eq : (n.choose k) * ((n - k).choose k) * ((n + k).choose k) =
                  ((n + k).choose k) * (n.choose k) * ((n - k).choose k) := by
    ring
  rw [h_rhs_eq, h_rhs_eq2, h_rhs_eq3, h_rhs_eq4, h_lhs_eq]

theorem a_eq_sum (n : ℕ) :
  a n = (range (n + 1)).sum fun k => ((n + k).choose (3 * k)) * ((3 * k).choose k) * ((2 * k).choose k) := by
  simp_rw [a, choose_identity]

theorem oeis_208425_conjecture_0 (p : ℕ) (hp : p.Prime) (hpgt3 : p > 3) (n : ℕ) (hn : n > 0) :
  padicValRat p (((a (p * n) : ℚ) - (a n : ℚ)) / ((p * n : ℚ) ^ 3)) ≥ 0 :=
by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have hb_ne : ((p * n : ℤ) ^ 3) ≠ 0 := by
    have hp_pos : p ≠ 0 := hp.ne_zero
    have hn_pos : n ≠ 0 := by omega
    have h_pn : p * n ≠ 0 := mul_ne_zero hp_pos hn_pos
    exact pow_ne_zero 3 (by exact_mod_cast h_pn)
  have h_eq : (((a (p * n) : ℚ) - (a n : ℚ)) / ((p * n : ℚ) ^ 3)) = (((a (p * n) : ℤ) - (a n : ℤ) : ℚ) / (((p * n : ℤ) ^ 3) : ℚ)) := by
    push_cast
    rfl
  rw [h_eq]
  rw [← Int.cast_pow]
  rw [← Int.cast_sub]
  apply padicValRat_ge_zero_of_dvd p ((a (p * n) : ℤ) - (a n : ℤ)) ((p * n : ℤ) ^ 3) hb_ne
  sorry
