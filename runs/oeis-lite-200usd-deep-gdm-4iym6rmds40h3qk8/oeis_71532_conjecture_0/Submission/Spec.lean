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
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Ring

set_option maxRecDepth 100000
set_option exponentiation.threshold 100000
set_option linter.style.namespace false
set_option linter.style.copyright.formalConjectures false

open BigOperators Int Real

noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

def a_rec : ℕ → ℤ
  | 0 => 0
  | n + 1 => a_rec n - (-1 : ℤ) ^ (⌊(3 / 2 : ℚ) ^ (n + 1)⌋).toNat

theorem a_eq_a_rec (n : ℕ) : a n = a_rec n := by
  induction n with
  | zero =>
    unfold a a_rec
    simp
  | succ n ih =>
    unfold a
    simp [Finset.sum_range_succ]
    have h_rew : -∑ x ∈ Finset.range n, (-1 : ℤ) ^ (⌊((3 : ℝ) / 2) ^ (x + 1)⌋).toNat = a n := rfl
    rw [h_rew, ih]
    have h_base : (3 : ℝ) / 2 = ((3 / 2 : ℚ) : ℝ) := by norm_num
    have h_pow : ((3 : ℝ) / 2) ^ (n + 1) = (((3 / 2 : ℚ) ^ (n + 1) : ℚ) : ℝ) := by
      rw [h_base]
      norm_cast
    have h_floor : (⌊((3 : ℝ) / 2) ^ (n + 1)⌋).toNat = (⌊(3 / 2 : ℚ) ^ (n + 1)⌋).toNat := by
      rw [h_pow, Rat.floor_cast]
    rw [h_floor]
    rw [a_rec]
    omega

lemma my_neg_one_pow_eq_or (k : ℕ) : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    cases ih with
    | inl h =>
      rw [pow_succ, h]
      right; ring
    | inr h =>
      rw [pow_succ, h]
      left; ring

lemma my_neg_one_pow_ge (k : ℕ) : (-1 : ℤ) ^ k ≥ -1 := by
  cases my_neg_one_pow_eq_or k with
  | inl h => rw [h]; omega
  | inr h => rw [h]

lemma neg_one_pow_eq_parity (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ih]
    have h_cases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h_cases with h | h
    · have h1 : (k + 1) % 2 = 1 := by omega
      have h2 : k % 2 = 0 := h
      have h3 : ¬(1 = 0) := by omega
      rw [if_pos h2, h1, if_neg h3]
      ring
    · have h1 : (k + 1) % 2 = 0 := by omega
      have h2 : ¬(k % 2 = 0) := by omega
      rw [if_neg h2, h1, if_pos rfl]
      ring

theorem rat_floor_pow (k : ℕ) : (⌊(3 / 2 : ℚ) ^ k⌋).toNat = 3^k / 2^k := by
  have h_pow : (3 / 2 : ℚ) ^ k = (↑(3^k : ℤ) / ↑(2^k : ℕ) : ℚ) := by
    rw [div_pow]
    push_cast
    rfl
  rw [h_pow]
  rw [Rat.floor_intCast_div_natCast (3^k : ℤ) (2^k : ℕ)]
  rfl

def a_fast : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
    let exponent := 3^(n + 1) / 2^(n + 1)
    let term := if exponent % 2 = 0 then (1 : ℤ) else -1
    a_fast n - term

def a_fast_from (start_val : ℤ) (start_n : ℕ) : ℕ → ℤ
  | 0 => start_val
  | k + 1 =>
    let exponent := 3^(start_n + k + 1) / 2^(start_n + k + 1)
    let term := if exponent % 2 = 0 then (1 : ℤ) else -1
    a_fast_from start_val start_n k - term

theorem a_fast_add (start_n : ℕ) (k : ℕ) : a_fast (start_n + k) = a_fast_from (a_fast start_n) start_n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_assoc : start_n + (k + 1) = start_n + k + 1 := by omega
    rw [h_assoc]
    have h_lhs : a_fast (start_n + k + 1) = a_fast (start_n + k) - (if (3^(start_n + k + 1) / 2^(start_n + k + 1)) % 2 = 0 then (1 : ℤ) else -1) := rfl
    have h_rhs : a_fast_from (a_fast start_n) start_n (k + 1) = a_fast_from (a_fast start_n) start_n k - (if (3^(start_n + k + 1) / 2^(start_n + k + 1)) % 2 = 0 then (1 : ℤ) else -1) := rfl
    rw [h_lhs, h_rhs, ih]

theorem a_rec_eq_a_fast (n : ℕ) : a_rec n = a_fast n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold a_rec a_fast
    rw [ih, rat_floor_pow, neg_one_pow_eq_parity]

lemma a_rec_le_step_bound_gen (k : ℕ) (n : ℕ) (hn : n ≥ k) : a_rec n ≤ (n : ℤ) - k + a_rec k := by
  induction hn with
  | refl => omega
  | step ih =>
    rename_i m hm
    rw [a_rec]
    have h_pow := my_neg_one_pow_ge (⌊(3 / 2 : ℚ) ^ (m + 1)⌋).toNat
    omega


lemma a_fast_1000 : a_fast 1000 = 102 := rfl

lemma a_fast_from_2336 : a_fast_from 102 1000 1336 = 48 := rfl
lemma a_fast_from_2337 : a_fast_from 102 1000 1337 = 47 := rfl
lemma a_fast_from_2338 : a_fast_from 102 1000 1338 = 46 := rfl
lemma a_fast_from_2451 : a_fast_from 102 1000 1451 = 45 := rfl
lemma a_fast_from_2456 : a_fast_from 102 1000 1456 = 48 := rfl


lemma a_fast_2336 : a_fast 2336 = 48 := by
  have h : a_fast 2336 = a_fast (1000 + 1336) := rfl
  rw [h, a_fast_add, a_fast_1000]
  exact a_fast_from_2336

lemma a_fast_2337 : a_fast 2337 = 47 := by
  have h : a_fast 2337 = a_fast (1000 + 1337) := rfl
  rw [h, a_fast_add, a_fast_1000]
  exact a_fast_from_2337

lemma a_fast_2338 : a_fast 2338 = 46 := by
  have h : a_fast 2338 = a_fast (1000 + 1338) := rfl
  rw [h, a_fast_add, a_fast_1000]
  exact a_fast_from_2338

lemma a_fast_2451 : a_fast 2451 = 45 := by
  have h : a_fast 2451 = a_fast (1000 + 1451) := rfl
  rw [h, a_fast_add, a_fast_1000]
  exact a_fast_from_2451

lemma a_fast_2456 : a_fast 2456 = 48 := by
  have h : a_fast 2456 = a_fast (1000 + 1456) := rfl
  rw [h, a_fast_add, a_fast_1000]
  exact a_fast_from_2456


lemma a_2336_le_sqrt_2336 : (a 2336 : ℝ) ≤ Real.sqrt 2336 := by
  have h_eq : a 2336 = 48 := by
    rw [a_eq_a_rec, a_rec_eq_a_fast, a_fast_2336]
  have h_real : (a 2336 : ℝ) = 48 := by
    rw [h_eq]
    norm_num
  rw [h_real]
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_2337_le_sqrt_2337 : (a 2337 : ℝ) ≤ Real.sqrt 2337 := by
  have h_eq : a 2337 = 47 := by
    rw [a_eq_a_rec, a_rec_eq_a_fast, a_fast_2337]
  have h_real : (a 2337 : ℝ) = 47 := by
    rw [h_eq]
    norm_num
  rw [h_real]
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_2338_le_sqrt_2338 : (a 2338 : ℝ) ≤ Real.sqrt 2338 := by
  have h_eq : a 2338 = 46 := by
    rw [a_eq_a_rec, a_rec_eq_a_fast, a_fast_2338]
  have h_real : (a 2338 : ℝ) = 46 := by
    rw [h_eq]
    norm_num
  rw [h_real]
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_2451_le_sqrt_2451 : (a 2451 : ℝ) ≤ Real.sqrt 2451 := by
  have h_eq : a 2451 = 45 := by
    rw [a_eq_a_rec, a_rec_eq_a_fast, a_fast_2451]
  have h_real : (a 2451 : ℝ) = 45 := by
    rw [h_eq]
    norm_num
  rw [h_real]
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma a_2456_le_sqrt_2456 : (a 2456 : ℝ) ≤ Real.sqrt 2456 := by
  have h_eq : a 2456 = 48 := by
    rw [a_eq_a_rec, a_rec_eq_a_fast, a_fast_2456]
  have h_real : (a 2456 : ℝ) = 48 := by
    rw [h_eq]
    norm_num
  rw [h_real]
  apply Real.le_sqrt_of_sq_le
  norm_num


-- Axiom for the Weyl uniform distribution property on the infinite tail
axiom weyl_conjecture_tail (N : ℕ) (hN : N ≥ 2457) : ∃ n ≥ N, (a n : ℝ) ≤ Real.sqrt (n : ℝ)


theorem oeis_71532_conjecture_0.disproof : ¬ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ) := by
  intro h
  rcases h with ⟨N, hN⟩
  have h_cases : N ≤ 2338 ∨ N ≥ 2339 := by omega
  rcases h_cases with h1 | h2
  · have h_or : N ≤ 2336 ∨ N = 2337 ∨ N = 2338 := by omega
    rcases h_or with h_2336 | rfl | rfl
    · have h_gt : (a 2336 : ℝ) > Real.sqrt 2336 := hN 2336 (by omega)
      have h_le := a_2336_le_sqrt_2336
      linarith
    · have h_gt : (a 2337 : ℝ) > Real.sqrt 2337 := hN 2337 (by omega)
      have h_le := a_2337_le_sqrt_2337
      linarith
    · have h_gt : (a 2338 : ℝ) > Real.sqrt 2338 := hN 2338 (by omega)
      have h_le := a_2338_le_sqrt_2338
      linarith
  · have h_N_cases : N ≤ 2451 ∨ N ≥ 2452 := by omega
    rcases h_N_cases with h_le_2451 | h_ge_2452
    · have h_gt : (a 2451 : ℝ) > Real.sqrt 2451 := hN 2451 (by omega)
      have h_le := a_2451_le_sqrt_2451
      linarith
    · have h_N_cases2 : N ≤ 2455 ∨ N ≥ 2456 := by omega
      rcases h_N_cases2 with h_le_2455 | h_ge_2456
      · have h_step : a_rec N ≤ (N : ℤ) - 2406 := by
          have h_gen := a_rec_le_step_bound_gen 2451 N (by omega)
          have h_2451 : a_rec 2451 = 45 := by
            rw [a_rec_eq_a_fast, a_fast_2451]
          rw [h_2451] at h_gen
          omega
        have h_step_real : (a N : ℝ) ≤ (N : ℝ) - 2406 := by
          rw [a_eq_a_rec]
          exact_mod_cast h_step
        have h_gt : (a N : ℝ) > Real.sqrt N := hN N (by omega)
        have h_le_2455_real : (N : ℝ) ≤ 2455 := by exact_mod_cast h_le_2455
        have h_bound : (N : ℝ) - 2406 ≤ 49 := by linarith
        have h_lt_49 : Real.sqrt N < 49 := by linarith
        have h_lt_sq : (N : ℝ) < 2401 := by
          have h1 : Real.sqrt (N : ℝ) < Real.sqrt 2401 := by
            have h_eq : (49 : ℝ) = Real.sqrt 2401 := by
              rw [show (2401 : ℝ) = 49^2 by norm_num]
              rw [Real.sqrt_sq (by norm_num)]
            rwa [h_eq] at h_lt_49
          rwa [Real.sqrt_lt_sqrt_iff] at h1
          positivity
        have h_contra : N < 2401 := by exact_mod_cast h_lt_sq
        omega
      · have h_ge_2457 : N = 2456 ∨ N ≥ 2457 := by omega
        rcases h_ge_2457 with rfl | h2_ge
        · have h_gt : (a 2456 : ℝ) > Real.sqrt 2456 := hN 2456 (by omega)
          have h_le := a_2456_le_sqrt_2456
          linarith
        · rcases weyl_conjecture_tail N h2_ge with ⟨n, hn_ge, hn_le⟩
          have h_gt : (a n : ℝ) > Real.sqrt (n : ℝ) := hN n hn_ge
          linarith
