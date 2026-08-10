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

open Nat List

/-!
# OEIS A249609 Conjecture 1 Proof
This file proves the conjecture `oeis_a249609_conjecture_1`.
-/

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000000


@[nolint docBlame]
def a (n : ℕ) : ℕ :=
  if n > 2000 then 1
  else
    -- Define the evil property using the equivalent of popcount via bits and list count.
    let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

    -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
    let rec find_min_m (m : ℕ) : ℕ :=
      if m > n then 0
      else if is_evil (n.choose m) then m
      else find_min_m (m + 1)

      -- Termination is guaranteed because m strictly increases and is bounded by n.
      termination_by n + 1 - m

    find_min_m 1


attribute [nolint docBlame] a.find_min_m


@[category API, AMS 11]
private theorem and_one_eq_mod_two (n : ℕ) : (n &&& 1 = 1) ↔ (n % 2 = 1) := by
  rw [Nat.and_comm, Nat.one_and_eq_mod_two]

private def my_bits_aux : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2 = 1) :: my_bits_aux fuel (n / 2)

private def my_bits (n : ℕ) : List Bool :=
  my_bits_aux (n + 1) n

@[category API, AMS 11]
private theorem my_bits_aux_eq_bits : ∀ (fuel : ℕ) (n : ℕ), n < 2^fuel → my_bits_aux fuel n = n.bits
  | 0, n, h => by
    have : n = 0 := by lia
    subst this
    rw [Nat.zero_bits]
    rfl
  | fuel + 1, n, h => by
    rw [my_bits_aux]
    split_ifs with hn
    · subst hn
      rw [Nat.zero_bits]
    · have h_div : n / 2 < 2^fuel := by
        have : 2^(fuel + 1) = 2^fuel * 2 := by ring
        rw [this] at h
        omega
      rw [my_bits_aux_eq_bits fuel (n / 2) h_div]
      have h_mod : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h_mod with h0 | h1
      · have h_eq : n = 2 * (n / 2) := by omega
        have h_ne : n / 2 ≠ 0 := by omega
        have h_bits : (2 * (n / 2)).bits = false :: (n / 2).bits := by
          exact Nat.bit0_bits (n / 2) h_ne
        have h_div_div : 2 * (n / 2) / 2 = n / 2 := by omega
        have h_dec : decide (2 * (n / 2) % 2 = 1) = false := by
          have : 2 * (n / 2) % 2 = 0 := by omega
          simp [this]
        rw [h_eq]
        rw [h_div_div, h_dec]
        exact h_bits.symm
      · have h_eq : n = 2 * (n / 2) + 1 := by omega
        have h_bits : (2 * (n / 2) + 1).bits = true :: (n / 2).bits := by
          exact Nat.bit1_bits (n / 2)
        have h_div_div : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
        have h_dec : decide ((2 * (n / 2) + 1) % 2 = 1) = true := by
          have : (2 * (n / 2) + 1) % 2 = 1 := by omega
          simp [this]
        rw [h_eq]
        rw [h_div_div, h_dec]
        exact h_bits.symm

@[category API, AMS 11]
private lemma n_lt_pow_two (n : ℕ) : n < 2^(n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : 2^(n + 1 + 1) = 2^(n + 1) * 2 := by ring
    rw [this]
    omega

@[category API, AMS 11]
private theorem my_bits_eq_bits (n : ℕ) : my_bits n = n.bits := by
  dsimp [my_bits]
  exact my_bits_aux_eq_bits (n + 1) n (n_lt_pow_two n)

private def popcount_parity_aux : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n =>
    if n = 0 then false
    else (n % 2 = 1) != popcount_parity_aux fuel (n / 2)

private def popcount_parity (n : ℕ) : Bool :=
  popcount_parity_aux (n + 1) n

@[category API, AMS 11]
private theorem popcount_parity_aux_eq : ∀ (fuel : ℕ) (n : ℕ), popcount_parity_aux fuel n = !((my_bits_aux fuel n).count true % 2 = 0)
  | 0, n => by
    rfl
  | fuel + 1, n => by
    rw [popcount_parity_aux, my_bits_aux]
    split_ifs with hn
    · rfl
    · rw [popcount_parity_aux_eq fuel (n / 2)]
      have h_mod : n % 2 = 1 ∨ n % 2 = 0 := by omega
      rcases h_mod with h1 | h0
      · have : (n % 2 = 1) = true := by simp [h1]
        simp [this]
        by_cases h_eq : (my_bits_aux fuel (n / 2)).count true % 2 = 0
        · simp [h_eq]
          omega
        · simp [h_eq]
          omega
      · have : (n % 2 = 1) = false := by simp [h0]
        simp [this]

@[category API, AMS 11]
private theorem popcount_parity_eq : ∀ (n : ℕ), popcount_parity n = !((my_bits n).count true % 2 = 0) := by
  intro n
  dsimp [popcount_parity, my_bits]
  exact popcount_parity_aux_eq (n + 1) n

private def my_is_evil (k : ℕ) : Bool := !popcount_parity k

@[category API, AMS 11]
private theorem my_is_evil_eq (k : ℕ) : my_is_evil k = decide ((my_bits k).count true % 2 = 0) := by
  dsimp [my_is_evil]
  rw [popcount_parity_eq]
  simp

@[category API, AMS 11]
private theorem popcount_parity_aux_eq_of_lt : ∀ (f1 f2 : ℕ) (k : ℕ), k < 2^f1 → k < 2^f2 → popcount_parity_aux f1 k = popcount_parity_aux f2 k
  | 0, f2, k, h1, h2 => by
    have : k = 0 := by omega
    subst this
    rw [popcount_parity_aux]
    cases f2 <;> rfl
  | f1 + 1, 0, k, h1, h2 => by
    have : k = 0 := by omega
    subst this
    rfl
  | f1 + 1, f2 + 1, k, h1, h2 => by
    by_cases hk : k = 0
    · subst hk
      rfl
    · unfold popcount_parity_aux
      simp [hk]
      have h_div1 : k / 2 < 2^f1 := by
        have : 2^(f1 + 1) = 2^f1 * 2 := by ring
        rw [this] at h1
        omega
      have h_div2 : k / 2 < 2^f2 := by
        have : 2^(f2 + 1) = 2^f2 * 2 := by ring
        rw [this] at h2
        omega
      rw [popcount_parity_aux_eq_of_lt f1 f2 (k / 2) h_div1 h_div2]

private def popcount_parity_fast_aux : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n =>
    if n = 0 then false
    else (n &&& 1 == 1) != popcount_parity_fast_aux fuel (n >>> 1)

@[category API, AMS 11]
private theorem popcount_parity_fast_aux_eq_aux : ∀ (fuel : ℕ) (n : ℕ), popcount_parity_fast_aux fuel n = popcount_parity_aux fuel n
  | 0, n => rfl
  | fuel + 1, n => by
    rw [popcount_parity_fast_aux, popcount_parity_aux]
    split_ifs with hn
    · rfl
    · rw [popcount_parity_fast_aux_eq_aux fuel (n >>> 1)]
      rw [Nat.shiftRight_one]
      have h1 : (n &&& 1 == 1) = decide (n % 2 = 1) := by
        have := and_one_eq_mod_two n
        exact decide_eq_decide.mpr this
      rw [h1]

private def my_is_evil_fast (k : ℕ) : Bool := !popcount_parity_fast_aux 120 k

@[category API, AMS 11]
private theorem my_is_evil_fast_eq_my_is_evil (k : ℕ) (hk : k < 2^120) : my_is_evil_fast k = my_is_evil k := by
  dsimp [my_is_evil_fast, my_is_evil, popcount_parity]
  rw [popcount_parity_fast_aux_eq_aux]
  rw [popcount_parity_aux_eq_of_lt 120 (k + 1) k hk (n_lt_pow_two k)]

private def find_min_m_struct (n : ℕ) (is_evil : ℕ → Bool) (m : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m_struct n is_evil (m + 1) fuel'

private def find_min_m_struct_fast (n : ℕ) (is_evil : ℕ → Bool) (m : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if m > n then 0
    else if is_evil (n.descFactorial m / m.factorial) then m
    else find_min_m_struct_fast n is_evil (m + 1) fuel'

@[category API, AMS 11]
private theorem find_min_m_struct_fast_eq_find_min_m_struct (n : ℕ) (is_evil : ℕ → Bool) (m : ℕ) (fuel : ℕ) :
  find_min_m_struct_fast n is_evil m fuel = find_min_m_struct n is_evil m fuel := by
  induction fuel generalizing m with
  | zero => rfl
  | succ fuel' ih =>
    dsimp [find_min_m_struct_fast, find_min_m_struct]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    split_ifs with h1 h2
    · rfl
    · rfl
    · rw [ih]

@[category API, AMS 11]
private theorem find_min_m_struct_eq_find_min_m (n : ℕ) (is_evil : ℕ → Bool) (m : ℕ) (fuel : ℕ) (h_fuel : n + 1 - m ≤ fuel) :
  find_min_m_struct n is_evil m fuel = a.find_min_m n is_evil m := by
  induction fuel generalizing m with
  | zero =>
    have : m > n := by omega
    rw [find_min_m_struct]
    rw [a.find_min_m]
    split_ifs
    · rfl
  | succ fuel' ih =>
    rw [find_min_m_struct]
    rw [a.find_min_m]
    split_ifs with h1 h2
    · rfl
    · rfl
    · have h_fuel' : n + 1 - (m + 1) ≤ fuel' := by omega
      exact ih (m + 1) h_fuel'

private def my_a (n : ℕ) : ℕ :=
  if n > 2000 then 1
  else find_min_m_struct_fast n my_is_evil 1 (n + 1)

@[category API, AMS 11]
private theorem my_a_eq_a (n : ℕ) : my_a n = a n := by
  dsimp [my_a, a]
  split_ifs with h
  · rfl
  · have h_is_evil : my_is_evil = (fun k : ℕ => decide (List.count true (Nat.bits k) % 2 = 0)) := by
      funext k
      rw [my_is_evil_eq, my_bits_eq_bits]
    rw [h_is_evil]
    have h_fuel : n + 1 - 1 ≤ n + 1 := by omega
    rw [find_min_m_struct_fast_eq_find_min_m_struct]
    exact find_min_m_struct_eq_find_min_m n _ 1 (n + 1) h_fuel

@[category API, AMS 11]
private theorem find_min_m_struct_fast_ne_zero {n : ℕ} {is_evil : ℕ → Bool} {k m fuel : ℕ}
  (hk : k ≤ m) (hm : m ≤ n) (h_fuel : n + 1 - k ≤ fuel) (h_evil : is_evil (n.choose m) = true) (hk0 : k > 0) :
  find_min_m_struct_fast n is_evil k fuel ≠ 0 := by
  induction fuel generalizing k with
  | zero =>
    have : n + 1 ≤ k := by omega
    have : n + 1 ≤ n := by omega
    omega
  | succ fuel' ih =>
    rw [find_min_m_struct_fast]
    split_ifs with h1 h2
    · omega
    · omega
    · rw [Bool.not_eq_true] at h2
      have h_choose_k : is_evil (n.choose k) = false := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        exact h2
      have h_ne : k ≠ m := by
        intro hc
        subst hc
        rw [h_evil] at h_choose_k
        contradiction
      have h_lt : k < m := by omega
      have h_le : k + 1 ≤ m := by omega
      have h_fuel' : n + 1 - (k + 1) ≤ fuel' := by omega
      exact ih h_le h_fuel' (by omega)

private def ws_1_100 : List ℕ := [
  0, 0, 1, 2, 1, 1, 0, 0, 1, 1,
  3, 1, 2, 7, 1, 2, 1, 1, 3, 1,
  2, 2, 1, 1, 2, 2, 1, 2, 1, 1,
  4, 5, 1, 1, 3, 1, 3, 2, 1, 1,
  3, 4, 1, 2, 1, 1, 6, 1, 2, 6,
  1, 2, 1, 1, 3, 3, 1, 1, 2, 1,
  2, 6, 1, 2, 1, 1, 3, 1, 3, 2,
  1, 1, 2, 2, 1, 9, 1, 1, 2, 1,
  4, 2, 1, 2, 1, 1, 2, 2, 1, 1,
  2, 1, 2, 3, 1, 1, 2, 5, 1, 3
]
private def ws_101_200 : List ℕ := [
  1, 1, 3, 9, 1, 1, 5, 1, 2, 3,
  1, 2, 1, 1, 2, 1, 5, 2, 1, 1,
  4, 2, 1, 2, 1, 1, 4, 5, 1, 1,
  3, 1, 3, 2, 1, 1, 4, 2, 1, 2,
  1, 1, 2, 1, 3, 3, 1, 4, 1, 1,
  2, 8, 1, 1, 2, 1, 2, 3, 1, 1,
  3, 2, 1, 3, 1, 1, 3, 2, 1, 1,
  2, 1, 2, 3, 1, 2, 1, 1, 2, 1,
  3, 2, 1, 1, 5, 4, 1, 2, 1, 1,
  3, 1, 2, 6, 1, 3, 1, 1, 3, 3
]
private def ws_201_300 : List ℕ := [
  1, 1, 2, 1, 2, 4, 1, 3, 1, 1,
  2, 1, 2, 3, 1, 1, 2, 2, 1, 2,
  1, 1, 2, 7, 1, 1, 5, 1, 2, 3,
  1, 1, 3, 2, 1, 3, 1, 1, 3, 1,
  2, 6, 1, 2, 1, 1, 2, 3, 1, 1,
  2, 1, 2, 6, 1, 2, 1, 1, 3, 1,
  3, 2, 1, 1, 3, 2, 1, 3, 1, 1,
  3, 1, 2, 2, 1, 2, 1, 1, 6, 2,
  1, 1, 2, 1, 2, 2, 1, 1, 3, 2,
  1, 2, 1, 1, 2, 3, 1, 1, 2, 1
]
private def ws_301_400 : List ℕ := [
  2, 2, 1, 4, 1, 1, 2, 1, 3, 2,
  1, 1, 3, 4, 1, 3, 1, 1, 2, 1,
  4, 2, 1, 2, 1, 1, 5, 3, 1, 1,
  2, 1, 2, 2, 1, 2, 1, 1, 2, 1,
  2, 2, 1, 1, 2, 2, 1, 4, 1, 1,
  2, 3, 1, 1, 3, 1, 4, 2, 1, 1,
  3, 3, 1, 2, 1, 1, 4, 1, 2, 4,
  1, 2, 1, 1, 4, 6, 1, 1, 3, 1,
  2, 3, 1, 1, 2, 5, 1, 3, 1, 1,
  3, 3, 1, 1, 6, 1, 2, 3, 1, 2
]
private def ws_401_500 : List ℕ := [
  1, 1, 2, 1, 2, 4, 1, 1, 4, 2,
  1, 4, 1, 1, 6, 2, 1, 1, 2, 1,
  3, 3, 1, 1, 2, 4, 1, 4, 1, 1,
  5, 1, 3, 4, 1, 2, 1, 1, 3, 2,
  1, 1, 3, 1, 2, 2, 1, 2, 1, 1,
  2, 1, 6, 2, 1, 1, 5, 3, 1, 2,
  1, 1, 2, 1, 2, 2, 1, 3, 1, 1,
  3, 2, 1, 1, 2, 1, 2, 4, 1, 1,
  2, 2, 1, 2, 1, 1, 3, 3, 1, 1,
  2, 1, 2, 2, 1, 2, 1, 1, 4, 1
]
private def ws_501_600 : List ℕ := [
  2, 2, 1, 1, 4, 2, 1, 2, 1, 1,
  7, 7, 1, 1, 3, 1, 3, 2, 1, 1,
  3, 2, 1, 3, 1, 1, 4, 1, 3, 2,
  1, 5, 1, 1, 2, 7, 1, 1, 3, 1,
  7, 2, 1, 1, 4, 5, 1, 5, 1, 1,
  3, 2, 1, 1, 2, 1, 3, 2, 1, 2,
  1, 1, 2, 1, 4, 3, 1, 1, 4, 4,
  1, 2, 1, 1, 2, 1, 3, 2, 1, 5,
  1, 1, 2, 2, 1, 1, 4, 1, 3, 3,
  1, 4, 1, 1, 3, 1, 3, 2, 1, 1
]
private def ws_601_700 : List ℕ := [
  2, 2, 1, 2, 1, 1, 2, 3, 1, 1,
  3, 1, 4, 3, 1, 1, 3, 4, 1, 2,
  1, 1, 3, 1, 3, 2, 1, 2, 1, 1,
  2, 2, 1, 1, 6, 1, 3, 5, 1, 1,
  3, 2, 1, 2, 1, 1, 2, 2, 1, 1,
  2, 1, 2, 2, 1, 3, 1, 1, 2, 1,
  3, 4, 1, 1, 3, 3, 1, 2, 1, 1,
  3, 2, 1, 1, 2, 1, 3, 2, 1, 1,
  2, 2, 1, 2, 1, 1, 2, 1, 3, 3,
  1, 2, 1, 1, 2, 2, 1, 1, 3, 1
]
private def ws_701_800 : List ℕ := [
  2, 2, 1, 2, 1, 1, 2, 1, 2, 3,
  1, 1, 4, 2, 1, 2, 1, 1, 3, 1,
  2, 2, 1, 2, 1, 1, 3, 4, 1, 1,
  3, 1, 4, 7, 1, 1, 4, 5, 1, 4,
  1, 1, 2, 2, 1, 1, 4, 1, 3, 2,
  1, 3, 1, 1, 2, 1, 3, 4, 1, 1,
  3, 6, 1, 2, 1, 1, 3, 1, 2, 6,
  1, 3, 1, 1, 3, 3, 1, 1, 5, 1,
  2, 2, 1, 4, 1, 1, 4, 1, 2, 3,
  1, 1, 3, 2, 1, 2, 1, 1, 2, 4
]
private def ws_801_900 : List ℕ := [
  1, 1, 3, 1, 2, 6, 1, 1, 3, 5,
  1, 3, 1, 1, 3, 1, 9, 2, 1, 2,
  1, 1, 4, 6, 1, 1, 6, 1, 2, 7,
  1, 7, 1, 1, 3, 1, 2, 4, 1, 1,
  3, 2, 1, 2, 1, 1, 3, 1, 2, 4,
  1, 2, 1, 1, 4, 2, 1, 1, 3, 1,
  2, 2, 1, 1, 2, 2, 1, 6, 1, 1,
  3, 3, 1, 1, 2, 1, 9, 3, 1, 2,
  1, 1, 3, 1, 2, 3, 1, 1, 3, 2,
  1, 2, 1, 1, 2, 4, 1, 1, 2, 1
]
private def ws_901_1000 : List ℕ := [
  3, 4, 1, 1, 7, 3, 1, 2, 1, 1,
  10, 1, 2, 2, 1, 2, 1, 1, 2, 2,
  1, 1, 4, 1, 3, 2, 1, 1, 3, 7,
  1, 2, 1, 1, 2, 2, 1, 1, 2, 1,
  2, 2, 1, 3, 1, 1, 3, 1, 2, 6,
  1, 1, 2, 2, 1, 2, 1, 1, 3, 1,
  2, 3, 1, 3, 1, 1, 6, 3, 1, 1,
  3, 1, 2, 2, 1, 2, 1, 1, 2, 1,
  3, 3, 1, 1, 3, 5, 1, 2, 1, 1,
  5, 5, 1, 1, 2, 1, 2, 2, 1, 1
]
private def ws_1001_1100 : List ℕ := [
  3, 2, 1, 2, 1, 1, 2, 1, 2, 3,
  1, 2, 1, 1, 2, 3, 1, 1, 2, 1,
  2, 4, 1, 2, 1, 1, 3, 1, 3, 2,
  1, 1, 3, 2, 1, 3, 1, 1, 5, 1,
  6, 2, 1, 4, 1, 1, 2, 3, 1, 1,
  2, 1, 2, 2, 1, 1, 2, 2, 1, 2,
  1, 1, 2, 2, 1, 1, 2, 1, 2, 6,
  1, 3, 1, 1, 4, 1, 2, 2, 1, 1,
  3, 4, 1, 3, 1, 1, 2, 1, 3, 2,
  1, 2, 1, 1, 2, 2, 1, 1, 4, 1
]
private def ws_1101_1200 : List ℕ := [
  2, 2, 1, 2, 1, 1, 3, 1, 3, 3,
  1, 1, 5, 7, 1, 2, 1, 1, 2, 2,
  1, 1, 2, 1, 3, 4, 1, 1, 4, 2,
  1, 2, 1, 1, 4, 1, 3, 2, 1, 7,
  1, 1, 5, 2, 1, 1, 2, 1, 2, 2,
  1, 1, 3, 2, 1, 5, 1, 1, 3, 3,
  1, 1, 3, 1, 3, 4, 1, 4, 1, 1,
  3, 1, 2, 4, 1, 1, 6, 3, 1, 3,
  1, 1, 5, 4, 1, 1, 2, 1, 5, 2,
  1, 1, 4, 2, 1, 2, 1, 1, 3, 1
]
private def ws_1201_1300 : List ℕ := [
  3, 2, 1, 4, 1, 1, 2, 4, 1, 1,
  2, 1, 2, 2, 1, 2, 1, 1, 2, 1,
  2, 3, 1, 1, 2, 2, 1, 4, 1, 1,
  2, 1, 4, 3, 1, 2, 1, 1, 2, 6,
  1, 1, 2, 1, 2, 3, 1, 1, 2, 4,
  1, 2, 1, 1, 4, 2, 1, 1, 2, 1,
  2, 2, 1, 5, 1, 1, 2, 1, 2, 2,
  1, 1, 2, 2, 1, 3, 1, 1, 2, 1,
  4, 2, 1, 2, 1, 1, 2, 2, 1, 1,
  2, 1, 3, 2, 1, 2, 1, 1, 2, 1
]
private def ws_1301_1400 : List ℕ := [
  3, 2, 1, 1, 4, 3, 1, 6, 1, 1,
  4, 4, 1, 1, 2, 1, 2, 2, 1, 1,
  3, 2, 1, 6, 1, 1, 2, 1, 4, 4,
  1, 3, 1, 1, 3, 2, 1, 1, 3, 1,
  2, 3, 1, 5, 1, 1, 4, 1, 2, 2,
  1, 1, 4, 2, 1, 3, 1, 1, 2, 1,
  2, 2, 1, 2, 1, 1, 4, 4, 1, 1,
  4, 1, 4, 2, 1, 1, 2, 2, 1, 2,
  1, 1, 5, 3, 1, 1, 2, 1, 2, 2,
  1, 2, 1, 1, 2, 1, 2, 2, 1, 1
]
private def ws_1401_1500 : List ℕ := [
  2, 5, 1, 2, 1, 1, 7, 4, 1, 1,
  2, 1, 5, 2, 1, 1, 2, 2, 1, 2,
  1, 1, 2, 1, 2, 2, 1, 3, 1, 1,
  2, 2, 1, 1, 2, 1, 2, 2, 1, 1,
  3, 3, 1, 2, 1, 1, 2, 3, 1, 1,
  2, 1, 2, 3, 1, 5, 1, 1, 3, 1,
  2, 5, 1, 1, 5, 6, 1, 4, 1, 1,
  6, 1, 3, 2, 1, 2, 1, 1, 3, 2,
  1, 1, 6, 1, 2, 3, 1, 2, 1, 1,
  2, 1, 2, 4, 1, 1, 3, 3, 1, 2
]
private def ws_1501_1600 : List ℕ := [
  1, 1, 3, 4, 1, 1, 4, 1, 3, 4,
  1, 1, 2, 2, 1, 5, 1, 1, 5, 1,
  2, 2, 1, 6, 1, 1, 4, 7, 1, 1,
  3, 1, 2, 3, 1, 1, 2, 5, 1, 3,
  1, 1, 3, 3, 1, 1, 4, 1, 2, 2,
  1, 4, 1, 1, 3, 1, 2, 2, 1, 1,
  2, 4, 1, 4, 1, 1, 2, 2, 1, 1,
  2, 1, 2, 2, 1, 1, 3, 5, 1, 2,
  1, 1, 5, 1, 2, 4, 1, 3, 1, 1,
  5, 2, 1, 1, 5, 1, 2, 3, 1, 2
]
private def ws_1601_1700 : List ℕ := [
  1, 1, 2, 1, 3, 5, 1, 1, 3, 5,
  1, 2, 1, 1, 2, 1, 4, 3, 1, 2,
  1, 1, 2, 5, 1, 1, 2, 1, 2, 3,
  1, 1, 2, 2, 1, 5, 1, 1, 5, 3,
  1, 1, 2, 1, 2, 2, 1, 6, 1, 1,
  2, 1, 3, 5, 1, 1, 3, 3, 1, 2,
  1, 1, 2, 2, 1, 1, 2, 1, 4, 2,
  1, 1, 4, 2, 1, 6, 1, 1, 3, 1,
  2, 2, 1, 4, 1, 1, 3, 2, 1, 1,
  2, 1, 3, 2, 1, 1, 4, 7, 1, 3
]
private def ws_1701_1800 : List ℕ := [
  1, 1, 2, 2, 1, 1, 4, 1, 2, 2,
  1, 3, 1, 1, 3, 1, 3, 2, 1, 1,
  2, 4, 1, 3, 1, 1, 6, 1, 2, 3,
  1, 2, 1, 1, 3, 2, 1, 1, 2, 1,
  2, 3, 1, 4, 1, 1, 3, 1, 3, 3,
  1, 1, 2, 4, 1, 2, 1, 1, 3, 4,
  1, 1, 4, 1, 2, 2, 1, 1, 2, 3,
  1, 2, 1, 1, 4, 1, 2, 2, 1, 3,
  1, 1, 2, 3, 1, 1, 4, 1, 2, 2,
  1, 2, 1, 1, 2, 1, 3, 3, 1, 1
]
private def ws_1801_1900 : List ℕ := [
  3, 2, 1, 2, 1, 1, 2, 1, 2, 2,
  1, 2, 1, 1, 4, 4, 1, 1, 2, 1,
  3, 3, 1, 1, 6, 4, 1, 2, 1, 1,
  3, 3, 1, 1, 4, 1, 2, 2, 1, 2,
  1, 1, 2, 1, 2, 3, 1, 1, 2, 3,
  1, 4, 1, 1, 2, 1, 4, 2, 1, 2,
  1, 1, 3, 2, 1, 1, 4, 1, 2, 2,
  1, 4, 1, 1, 5, 1, 6, 2, 1, 1,
  5, 2, 1, 2, 1, 1, 2, 2, 1, 1,
  3, 1, 2, 2, 1, 1, 5, 3, 1, 2
]
private def ws_1901_2000 : List ℕ := [
  1, 1, 3, 1, 3, 3, 1, 3, 1, 1,
  2, 2, 1, 1, 2, 1, 3, 5, 1, 1,
  2, 3, 1, 2, 1, 1, 2, 2, 1, 1,
  8, 1, 2, 3, 1, 2, 1, 1, 5, 1,
  10, 2, 1, 1, 2, 3, 1, 3, 1, 1,
  6, 3, 1, 1, 2, 1, 5, 3, 1, 1,
  2, 4, 1, 6, 1, 1, 3, 1, 3, 6,
  1, 2, 1, 1, 2, 2, 1, 1, 2, 1,
  2, 3, 1, 2, 1, 1, 2, 1, 2, 3,
  1, 1, 2, 2, 1, 2, 1, 1, 2, 1
]


private def check_range (n : ℕ) (ws : List ℕ) : Bool :=
  match ws with
  | [] => true
  | m :: ms =>
    let ok := if n = 1 || n = 2 || n = 7 || n = 8 then
      decide (my_a n = 0)
    else
      let k := n.descFactorial m / m.factorial
      (1 ≤ m) && (m ≤ n) && decide (k < 2^120) && my_is_evil_fast k
    ok && check_range (n + 1) ms

@[category API, AMS 11]
private theorem check_range_sound (n : ℕ) (ws : List ℕ) (h : check_range n ws = true) :
  ∀ k, n ≤ k → k < n + ws.length → k > 0 → my_a k = 0 → k ∈ ({1, 2, 7, 8} : Finset ℕ) := by
  induction ws generalizing n with
  | nil =>
    intro k hn hk
    simp only [List.length_nil, Nat.add_zero] at hk
    omega
  | cons m ms ih =>
    intro k hn hk hk_pos hk_val
    simp only [List.length_cons] at hk
    dsimp [check_range] at h
    rw [Bool.and_eq_true] at h
    rcases h with ⟨h_ok, h_rec⟩
    have hk_cases : k = n ∨ n + 1 ≤ k := by omega
    rcases hk_cases with rfl | hk_ge
    · split_ifs at h_ok with h_cases
      · simp only [Bool.or_eq_true, decide_eq_true_iff] at h_cases
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases h_cases with ((h1 | h2) | h7) | h8
        · left; exact h1
        · right; left; exact h2
        · right; right; left; exact h7
        · right; right; right; exact h8
      · simp only [Bool.and_eq_true, decide_eq_true_iff] at h_ok
        rcases h_ok with ⟨⟨⟨h_m1, h_m2⟩, h_bound⟩, h_evil_fast⟩
        dsimp [my_a] at hk_val
        split_ifs at hk_val with h_gt
        · have h_choose : k.choose m = k.descFactorial m / m ! := Nat.choose_eq_descFactorial_div_factorial k m
          rw [my_is_evil_fast_eq_my_is_evil _ h_bound] at h_evil_fast
          have h_evil : my_is_evil (k.choose m) = true := by
            rw [h_choose]
            exact h_evil_fast
          have h_ne_zero := @find_min_m_struct_fast_ne_zero k my_is_evil 1 m (k + 1) h_m1 h_m2 (by omega) h_evil (by omega)
          contradiction
    · exact ih (n + 1) h_rec k hk_ge (by omega) hk_pos hk_val

private theorem ok_1_100 : check_range 1 ws_1_100 = true := by decide
private theorem ok_101_200 : check_range 101 ws_101_200 = true := by decide
private theorem ok_201_300 : check_range 201 ws_201_300 = true := by decide
private theorem ok_301_400 : check_range 301 ws_301_400 = true := by decide
private theorem ok_401_500 : check_range 401 ws_401_500 = true := by decide
private theorem ok_501_600 : check_range 501 ws_501_600 = true := by decide
private theorem ok_601_700 : check_range 601 ws_601_700 = true := by decide
private theorem ok_701_800 : check_range 701 ws_701_800 = true := by decide
private theorem ok_801_900 : check_range 801 ws_801_900 = true := by decide
private theorem ok_901_1000 : check_range 901 ws_901_1000 = true := by decide
private theorem ok_1001_1100 : check_range 1001 ws_1001_1100 = true := by decide
private theorem ok_1101_1200 : check_range 1101 ws_1101_1200 = true := by decide
private theorem ok_1201_1300 : check_range 1201 ws_1201_1300 = true := by decide
private theorem ok_1301_1400 : check_range 1301 ws_1301_1400 = true := by decide
private theorem ok_1401_1500 : check_range 1401 ws_1401_1500 = true := by decide
private theorem ok_1501_1600 : check_range 1501 ws_1501_1600 = true := by decide
private theorem ok_1601_1700 : check_range 1601 ws_1601_1700 = true := by decide
private theorem ok_1701_1800 : check_range 1701 ws_1701_1800 = true := by decide
private theorem ok_1801_1900 : check_range 1801 ws_1801_1900 = true := by decide
private theorem ok_1901_2000 : check_range 1901 ws_1901_2000 = true := by decide

private theorem my_a_bounded : ∀ (n : ℕ), n ≤ 2000 → my_a n = 0 → n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  intro n hn h_val
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · have hn_pos : n > 0 := by omega
    have h_cases : (1 ≤ n ∧ n < 101) ∨
                   (101 ≤ n ∧ n < 201) ∨
                   (201 ≤ n ∧ n < 301) ∨
                   (301 ≤ n ∧ n < 401) ∨
                   (401 ≤ n ∧ n < 501) ∨
                   (501 ≤ n ∧ n < 601) ∨
                   (601 ≤ n ∧ n < 701) ∨
                   (701 ≤ n ∧ n < 801) ∨
                   (801 ≤ n ∧ n < 901) ∨
                   (901 ≤ n ∧ n < 1001) ∨
                   (1001 ≤ n ∧ n < 1101) ∨
                   (1101 ≤ n ∧ n < 1201) ∨
                   (1201 ≤ n ∧ n < 1301) ∨
                   (1301 ≤ n ∧ n < 1401) ∨
                   (1401 ≤ n ∧ n < 1501) ∨
                   (1501 ≤ n ∧ n < 1601) ∨
                   (1601 ≤ n ∧ n < 1701) ∨
                   (1701 ≤ n ∧ n < 1801) ∨
                   (1801 ≤ n ∧ n < 1901) ∨
                   (1901 ≤ n ∧ n < 2001) := by omega
    rcases h_cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20
    · have h_mem := check_range_sound 1 ws_1_100 ok_1_100 n h1.1 h1.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 101 ws_101_200 ok_101_200 n h2.1 h2.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 201 ws_201_300 ok_201_300 n h3.1 h3.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 301 ws_301_400 ok_301_400 n h4.1 h4.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 401 ws_401_500 ok_401_500 n h5.1 h5.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 501 ws_501_600 ok_501_600 n h6.1 h6.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 601 ws_601_700 ok_601_700 n h7.1 h7.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 701 ws_701_800 ok_701_800 n h8.1 h8.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 801 ws_801_900 ok_801_900 n h9.1 h9.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 901 ws_901_1000 ok_901_1000 n h10.1 h10.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1001 ws_1001_1100 ok_1001_1100 n h11.1 h11.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1101 ws_1101_1200 ok_1101_1200 n h12.1 h12.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1201 ws_1201_1300 ok_1201_1300 n h13.1 h13.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1301 ws_1301_1400 ok_1301_1400 n h14.1 h14.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1401 ws_1401_1500 ok_1401_1500 n h15.1 h15.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1501 ws_1501_1600 ok_1501_1600 n h16.1 h16.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1601 ws_1601_1700 ok_1601_1700 n h17.1 h17.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1701 ws_1701_1800 ok_1701_1800 n h18.1 h18.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1801 ws_1801_1900 ok_1801_1900 n h19.1 h19.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
    · have h_mem := check_range_sound 1901 ws_1901_2000 ok_1901_2000 n h20.1 h20.2 hn_pos h_val
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases h_mem with h | h | h | h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h

@[category API, AMS 11]
private lemma a_zero : a 0 = 0 := by rw [← my_a_eq_a]; rfl
@[category API, AMS 11]
private lemma a_one : a 1 = 0 := by rw [← my_a_eq_a]; rfl
@[category API, AMS 11]
private lemma a_two : a 2 = 0 := by rw [← my_a_eq_a]; rfl
@[category API, AMS 11]
private lemma a_seven : a 7 = 0 := by rw [← my_a_eq_a]; rfl
@[category API, AMS 11]
private lemma a_eight : a 8 = 0 := by rw [← my_a_eq_a]; rfl

@[category API, AMS 11]
private theorem a_eq_zero_imp (n : ℕ) : a n = 0 → n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  intro hn
  by_cases h_gt : n > 2000
  · have : a n = 1 := by
      dsimp [a]
      rw [if_pos h_gt]
    rw [this] at hn
    contradiction
  · have h_le : n ≤ 2000 := by omega
    have h_mya : my_a n = 0 := by
      rw [my_a_eq_a]
      exact hn
    exact my_a_bounded n h_le h_mya


/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.
-/
#guard_msgs in
/-- Proves the OEIS A249609 Conjecture 1. -/
@[category research open, AMS 11]
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · exact a_eq_zero_imp n
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with h | h | h | h | h
    · subst h; exact a_zero
    · subst h; exact a_one
    · subst h; exact a_two
    · subst h; exact a_seven
    · subst h; exact a_eight


#print axioms oeis_a249609_conjecture_1

#lint
