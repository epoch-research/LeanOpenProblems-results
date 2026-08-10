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

open Nat
open Polynomial

/--
Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

/--
The polynomial associated with the $n$-th Apéry number:
$$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$$
-/
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma coeff_apery_poly_self (n : ℕ) : (apery_poly n).coeff n = ((2 * n).choose n : ℚ) := by
  unfold apery_poly
  rw [finset_sum_coeff]
  have h_eq : Finset.sum (Finset.range (n + 1)) (fun k ↦ coeff (C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * X ^ k) n) =
              coeff (C (((n.choose n) ^ 2 * ((n + n).choose n) : ℕ) : ℚ) * X ^ n) n := by
    apply Finset.sum_eq_single n
    · intro b hb hb_ne
      rw [coeff_C_mul_X_pow]
      split_ifs with h_eq
      · subst h_eq
        contradiction
      · rfl
    · intro hn
      rw [Finset.mem_range] at hn
      omega
  rw [h_eq]
  rw [coeff_C_mul_X_pow]
  simp
  have h2 : n + n = 2 * n := by ring
  rw [h2]

lemma coeff_apery_poly_zero (n : ℕ) : (apery_poly n).coeff 0 = 1 := by
  unfold apery_poly
  rw [finset_sum_coeff]
  have h_eq : Finset.sum (Finset.range (n + 1)) (fun k ↦ coeff (C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * X ^ k) 0) =
              coeff (C (((n.choose 0) ^ 2 * ((n + 0).choose 0) : ℕ) : ℚ) * X ^ 0) 0 := by
    apply Finset.sum_eq_single 0
    · intro b hb hb_ne
      rw [coeff_C_mul_X_pow]
      split_ifs with h_eq
      · subst h_eq
        contradiction
      · rfl
    · intro hn
      rw [Finset.mem_range] at hn
      have : 0 < n + 1 := by omega
      contradiction
  rw [h_eq]
  rw [coeff_C_mul_X_pow]
  simp

lemma apery_poly_ne_one (n : ℕ) (hn : 1 ≤ n) : apery_poly n ≠ 1 := by
  intro h
  have h_coeff : (apery_poly n).coeff n = (1 : ℚ[X]).coeff n := congr_arg (coeff · n) h
  rw [coeff_apery_poly_self, coeff_one] at h_coeff
  have hn_ne : n ≠ 0 := by omega
  split_ifs at h_coeff
  · contradiction
  · have h_pos : 1 ≤ (2 * n).choose n := Nat.choose_pos (by omega)
    have h_pos_q : (1 : ℚ) ≤ ((2 * n).choose n : ℚ) := by exact_mod_cast h_pos
    rw [h_coeff] at h_pos_q
    norm_num at h_pos_q

lemma apery_poly_ne_X (n : ℕ) : apery_poly n ≠ X := by
  intro h
  have h_coeff : (apery_poly n).coeff 0 = (X : ℚ[X]).coeff 0 := congr_arg (coeff · 0) h
  rw [coeff_apery_poly_zero] at h_coeff
  simp at h_coeff

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  sorry
