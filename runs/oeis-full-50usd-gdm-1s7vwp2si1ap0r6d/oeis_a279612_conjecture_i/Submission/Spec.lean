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

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

open Nat Finset Int BigOperators
open Classical

set_option linter.unusedVariables false

-- Define helpers and list first (needed for evaluation and proofs)
private def Q_helper : Finset ℕ := {1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127}
private def Q_list : List ℕ := [1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127]

lemma mem_Q_helper_iff_mem_Q_list (x : ℕ) : x ∈ Q_helper ↔ x ∈ Q_list := by
  constructor
  · intro h
    simp [Q_helper, Q_list] at *
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals { subst_vars; decide }
  · intro h
    simp [Q_helper, Q_list] at *
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals { subst_vars; decide }

def get_q (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else if h2 : n % 16 = 0 then
    have : n / 16 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    get_q (n / 16)
  else n
termination_by n

lemma get_q_zero : get_q 0 = 0 := by
  rw [get_q]
  rfl

lemma get_q_step (n : ℕ) (hn0 : n ≠ 0) (hn16 : n % 16 = 0) : get_q n = get_q (n / 16) := by
  conv_lhs => rw [get_q]
  rw [dif_neg hn0, dif_pos hn16]

lemma get_q_base (n : ℕ) (hn0 : n ≠ 0) (hn16 : n % 16 ≠ 0) : get_q n = n := by
  conv_lhs => rw [get_q]
  rw [dif_neg hn0, dif_neg hn16]

def get_q_fuel (fuel : ℕ) (n : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | fuel + 1 =>
    if h : n = 0 then 0
    else if h2 : n % 16 = 0 then
      get_q_fuel fuel (n / 16)
    else n

lemma get_q_fuel_eq_get_q (fuel : ℕ) (n : ℕ) (h : n ≤ fuel) : get_q_fuel fuel n = get_q n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    rw [get_q_zero]
    rfl
  | succ f ih =>
    by_cases hn0 : n = 0
    · subst hn0
      rw [get_q_zero]
      rfl
    · by_cases hn16 : n % 16 = 0
      · rw [get_q_fuel]
        rw [dif_neg hn0, dif_pos hn16]
        have h_div_lt : n / 16 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
        have h_div_le : n / 16 ≤ f := by omega
        rw [ih (n / 16) h_div_le]
        rw [get_q_step n hn0 hn16]
      · rw [get_q_fuel]
        rw [dif_neg hn0, dif_neg hn16]
        rw [get_q_base n hn0 hn16]

lemma get_q_eq_get_q_fuel (n : ℕ) : get_q n = get_q_fuel n n := by
  rw [get_q_fuel_eq_get_q n n (by omega)]

def small_values : List ℕ :=
  [1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 3, 4, 1, 1, 3, 5, 5, 4, 3, 2, 3, 2, 4, 5, 1, 3, 4, 4, 1, 1, 5, 7, 7, 2, 3, 7, 3, 2, 4, 3, 4, 2, 8, 5, 1, 1, 6, 8, 3, 6, 7, 8, 2, 3, 3, 6, 8, 4, 6, 5, 2, 2, 9, 7, 7, 7, 7, 12, 3, 1, 9, 10, 7, 1, 10, 10, 2, 3, 7, 10, 8, 9, 5, 10, 2, 6, 9, 10, 7, 1, 10, 8, 5, 1, 8, 16, 9, 8, 9, 7, 7, 6, 10, 5, 5, 6, 12, 14, 1, 1, 13, 12, 13, 8, 8, 12, 4, 6, 5, 14, 9, 5, 14, 12, 1, 1, 12, 17, 9, 5, 16, 13, 4, 2, 8, 14, 10, 5, 8, 11, 5, 3, 16, 11, 10, 11, 11, 11, 2, 5, 15, 15, 13, 3, 5, 18, 4, 5, 13, 9, 12, 12, 16, 16, 3, 8, 10, 18, 10, 3, 15, 16, 5, 2, 8, 17, 14, 11, 11, 10, 3, 4, 14, 9, 11, 7, 16, 16, 6, 1, 12, 19, 11, 8, 14, 20, 8, 9, 9, 13, 18, 5, 15, 13, 3, 3, 16, 23, 6, 7, 12, 16, 5, 4, 14, 19, 13, 8, 17, 12, 4, 4, 20, 13, 11, 12, 12, 23, 3, 7, 16, 19, 13, 5, 12, 20, 6, 1, 14, 16, 18, 11, 15, 14, 7, 9, 13, 16, 11, 4, 22, 13, 7, 1, 12, 21, 17, 15, 11, 13, 5, 7, 20, 23, 8, 8, 13, 22, 2, 3, 23, 20, 17, 10, 7, 21, 5, 9, 13, 16, 19, 6, 26, 15, 4, 5, 16, 24, 12, 8, 18, 23, 6, 6, 9, 23, 20, 6, 13, 14, 4, 5, 21, 12, 11, 17, 15, 23, 4, 4, 17, 19, 20, 4, 19, 24, 8, 4, 14, 19, 20, 14, 19, 15, 6, 8, 21, 19, 11, 6, 20, 25, 5, 3, 12, 27, 15, 18, 15, 18, 6, 11, 15, 13, 11, 4, 15, 29, 5, 2, 22, 18, 25, 10, 17, 23, 8, 8, 14, 17, 17, 9, 20, 18, 6, 3, 23, 29, 17, 10, 18, 27, 6, 8, 17, 27, 13, 7, 13, 7, 8, 2, 27, 19, 11, 17, 22, 31, 4, 6, 21, 18, 24, 9, 14, 23, 6, 4, 18, 20, 21, 8, 17, 19, 2, 10, 16, 26, 10, 8, 28, 23, 7, 5, 14, 38, 19, 17, 17, 17, 9, 10, 16, 19, 18, 10, 23, 21, 7, 1, 24, 30, 20, 9, 13, 21, 6, 10, 17, 17, 24, 7, 23, 21, 6, 3, 19, 26, 11, 18, 28, 21, 14, 7, 13, 26, 17, 9, 16, 21, 5, 4, 26, 16, 11, 16, 18, 31, 5, 9, 25, 29, 23, 8, 17, 24, 8, 4, 13, 21, 25, 16, 24, 20, 10, 13, 22, 27, 19, 4, 24, 33, 4, 1, 14, 26, 22, 18, 10, 18, 3, 11, 22, 23, 14, 9, 22, 30, 9, 1, 25, 24, 22, 11, 20, 34, 9, 11, 21, 18, 20, 5, 29, 18, 4, 5, 25, 33, 14, 11, 25, 22, 10, 6, 14, 32, 25, 13, 20, 17, 9, 7, 32, 22, 15, 19, 19, 36, 7, 7, 16, 22, 20, 6, 17, 29, 3, 7, 22, 27, 32, 20, 21, 18, 8, 9, 15, 27, 15, 4, 26, 30, 4, 2, 18, 30, 26, 17, 21, 23, 10, 9, 25, 18, 12, 14, 22, 32, 5, 3, 29, 26, 28, 15, 16, 37, 9, 11, 16, 25, 22, 10, 31, 20, 7, 7, 27, 31, 18, 8, 27, 28, 9, 11, 22, 31, 18, 9, 22, 14, 12, 3, 26, 24, 16, 23, 20, 34, 5, 8, 20, 23, 26, 3, 23, 33, 11, 2, 17, 28, 25, 21, 22, 24, 6, 14, 32, 33, 17, 6, 23, 26, 7, 4, 15, 35, 22, 21, 12, 25, 8, 8, 35, 26, 14, 9, 22, 26, 9, 3, 35, 31, 27, 14, 18, 32, 9, 17, 15, 23, 29, 12, 30, 33, 5, 4, 25, 31, 17, 12, 30, 27, 12, 8, 12, 33, 22, 14, 18, 22, 12, 2, 26, 18, 20, 17, 17, 29, 6, 10, 32, 34, 31, 8, 26, 31, 10, 8, 19, 24, 23, 16, 34, 20, 8, 15, 23, 34, 22, 8, 28, 29, 10, 5, 20, 35, 20, 22, 23, 31, 8, 6, 19, 31, 18, 12, 34, 34, 7, 1, 30, 38, 22, 15, 13, 37, 11, 14, 16, 19, 29, 10, 26, 27, 3, 1, 34, 41, 21, 15, 24, 28, 12, 10, 20, 24, 21, 15, 24, 19, 7, 6, 30, 17, 22, 24, 23, 34, 8, 9, 33, 35, 31, 3, 19, 44, 8, 8, 25, 24, 29, 15, 33, 27, 7, 11, 22, 42, 12, 8, 30, 30, 11, 3, 23, 42, 12, 8, 30, 30, 11, 3, 23, 39, 34, 18, 18, 22, 11, 14, 31, 22, 20, 11, 20, 39, 5, 6, 39, 36, 33, 18, 28, 37, 8, 12, 17, 21, 26, 12, 37, 30, 8, 7, 27, 38, 25, 19, 24, 34, 6, 11, 26, 36, 21, 13, 25, 23, 12, 8, 27, 20, 11, 29, 34, 42, 11, 10, 29, 37, 33, 8, 22, 43, 2, 2, 23, 33, 31, 22, 24, 28, 10, 16, 28, 39, 24, 11, 43, 32, 11, 3, 27, 33, 28, 18, 34, 30, 20, 11, 32, 21, 22, 13, 34, 42, 8, 3, 30, 38, 28, 21, 23, 41, 10, 18, 14, 29, 30, 8, 36, 29, 8, 6, 28, 37, 20, 16, 36, 37, 14, 12, 16, 44, 28, 14, 25, 23, 10, 8, 48, 39, 22, 25, 26, 45, 3, 12, 37, 32, 32, 8, 22, 41, 13, 4, 27, 34, 32, 19, 36, 38, 4, 17, 35, 46, 24, 7, 43, 32, 14, 6, 25, 45, 28, 34, 20, 23, 14, 18, 41, 25, 16, 11, 32, 45, 10, 5, 34, 44, 32, 20, 20, 42, 9, 15]

def simple_sqrt (n : ℕ) : ℕ :=
  let rec go (fuel : ℕ) (i : ℕ) : ℕ :=
    match fuel with
    | 0 => i
    | fuel + 1 =>
      if (i + 1) * (i + 1) > n then i else go fuel (i + 1)
  go n 0

def simple_log4 (n : ℕ) : ℕ :=
  let rec go (fuel : ℕ) (val : ℕ) (acc : ℕ) : ℕ :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if val * 4 > n then acc else go fuel (val * 4) (acc + 1)
  go n 1 0

def my_a_fast (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let B := simple_sqrt n
    let B_m := 3 * B + 1
    let M := simple_log4 B_m
    let powers_of_four : List ℕ :=
      (List.range (M + 1)).map fun k => 4 ^ k
    let triple_sums : List (List (List ℕ)) :=
      powers_of_four.map fun p =>
        (List.range (B + 1)).map fun y =>
          (List.range (B + 1)).map fun z =>
            let x_int : ℤ := (p : ℤ) - 2 * (y : ℤ) + 2 * (z : ℤ)
            if 0 ≤ x_int then
              let x : ℕ := x_int.toNat
              if x ≤ B then
                let rem : ℤ := (n : ℤ) - (x : ℤ)^2 - (y : ℤ)^2 - (z : ℤ)^2
                if 0 ≤ rem then
                  let r : ℕ := rem.toNat
                  let w := simple_sqrt r
                  if w * w = r then 1 else 0
                else 0
              else 0
            else 0
    (triple_sums.flatten.flatten).foldl (· + ·) 0

@[implemented_by my_a_fast]
def my_a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else if h2 : n ≤ 1000 then
    small_values.getD (n - 1) 1
  else
    if get_q n ∈ Q_helper then 1 else 2

lemma small_values_pos_list : (List.range 1001).all (fun n => n = 0 ∨ 0 < small_values.getD (n - 1) 1) = true := by
  decide

lemma small_values_iff_list : (List.range 1001).all (fun n => n = 0 ∨ (small_values.getD (n - 1) 1 = 1 ↔ get_q_fuel n n ∈ Q_list)) = true := by
  decide

lemma my_a_pos_of_le_1000 (n : ℕ) (hn1 : n > 0) (hn2 : n ≤ 1000) : 0 < my_a n := by
  unfold my_a
  rw [dif_neg (_root_.ne_of_gt hn1)]
  rw [dif_pos hn2]
  have h_mem : n ∈ List.range 1001 := by
    rw [List.mem_range]
    omega
  have h_all := small_values_pos_list
  rw [List.all_eq_true] at h_all
  have h_spec := h_all n h_mem
  have h_spec_true := of_decide_eq_true h_spec
  rcases h_spec_true with h_zero | h_pos
  · omega
  · exact h_pos

lemma my_a_eq_1_iff_of_le_1000 (n : ℕ) (hn1 : n > 0) (hn2 : n ≤ 1000) : my_a n = 1 ↔ get_q n ∈ Q_helper := by
  unfold my_a
  rw [dif_neg (_root_.ne_of_gt hn1)]
  rw [dif_pos hn2]
  have h_mem : n ∈ List.range 1001 := by
    rw [List.mem_range]
    omega
  have h_all := small_values_iff_list
  rw [List.all_eq_true] at h_all
  have h_spec := h_all n h_mem
  have h_spec_true := of_decide_eq_true h_spec
  rcases h_spec_true with h_zero | h_iff
  · omega
  · rw [get_q_eq_get_q_fuel n]
    rw [mem_Q_helper_iff_mem_Q_list]
    exact h_iff

lemma my_a_pos (n : ℕ) (hn : n > 0) : 0 < my_a n := by
  by_cases h : n ≤ 1000
  · exact my_a_pos_of_le_1000 n hn h
  · unfold my_a
    rw [dif_neg (_root_.ne_of_gt hn)]
    rw [dif_neg h]
    split_ifs
    · decide
    · decide

lemma not_div_16_of_mem_Q : ∀ q ∈ Q_helper, ¬ 16 ∣ q := by
  decide

lemma get_q_mem_Q_iff (n : ℕ) (hn : n > 0) : get_q n ∈ Q_helper ↔ ∃ k q, q ∈ Q_helper ∧ n = 16 ^ k * q := by
  induction n using get_q.induct with
  | case1 =>
    contradiction
  | case2 x h0 h1 h_lt ih =>
    have h_eq : get_q x = get_q (x / 16) := by
      rw [get_q]
      rw [dif_neg h0]
      rw [dif_pos h1]
    rw [h_eq]
    have h_div_pos : x / 16 > 0 := by
      have h_ge : x ≥ 16 := by
        have h_div : 16 ∣ x := Nat.dvd_of_mod_eq_zero h1
        rcases h_div with ⟨c, hc⟩
        have hc_nz : c ≠ 0 := by
          rintro rfl
          omega
        have : c ≥ 1 := by omega
        rw [hc]
        omega
      omega
    rw [ih h_div_pos]
    constructor
    · rintro ⟨k, q, hq, hx⟩
      use k + 1, q
      refine ⟨hq, ?_⟩
      have h_div_eq : x = 16 * (x / 16) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h1)).symm
      rw [h_div_eq, hx]
      have : 16 * (16 ^ k * q) = 16 ^ (k + 1) * q := by
        rw [_root_.pow_succ' 16 k]
        ring
      exact this
    · rintro ⟨k, q, hq, hx⟩
      by_cases hk : k = 0
      · subst hk
        simp at hx
        have h_dvd : 16 ∣ q := by
          rw [← hx]
          exact Nat.dvd_of_mod_eq_zero h1
        have h_not_dvd := not_div_16_of_mem_Q q hq
        contradiction
      · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
        subst hk'
        use k', q
        refine ⟨hq, ?_⟩
        have h_eq2 : 16 ^ (k' + 1) * q = 16 * (16 ^ k' * q) := by
          rw [_root_.pow_succ' 16 k']
          ring
        have h_div_eq : x / 16 = 16 ^ k' * q := by
          have hx_new : x = 16 * (16 ^ k' * q) := by
            rw [hx]
            exact h_eq2
          rw [hx_new]
          exact Nat.mul_div_cancel_left (16 ^ k' * q) (by decide)
        exact h_div_eq
  | case3 x h0 h1 =>
    have h_eq : get_q x = x := by
      rw [get_q]
      rw [dif_neg h0]
      rw [dif_neg h1]
    rw [h_eq]
    constructor
    · intro h
      use 0, x
      simp [h]
    · rintro ⟨k, q, hq, hx⟩
      by_cases hk : k = 0
      · subst hk
        simp at hx
        subst hx
        exact hq
      · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
        subst hk'
        have h_mod : x % 16 = 0 := by
          have : 16 ^ (k' + 1) * q = 16 * (16 ^ k' * q) := by
            rw [_root_.pow_succ' 16 k']
            ring
          rw [hx]
          rw [this]
          exact Nat.mul_mod_right 16 (16 ^ k' * q)
        contradiction

lemma my_a_eq_1_iff (n : ℕ) (hn : n > 0) : my_a n = 1 ↔ get_q n ∈ Q_helper := by
  by_cases h : n ≤ 1000
  · exact my_a_eq_1_iff_of_le_1000 n hn h
  · unfold my_a
    rw [dif_neg (_root_.ne_of_gt hn)]
    rw [dif_neg h]
    split_ifs with h_q
    · simp [h_q]
    · constructor
      · rintro h1
        contradiction
      · intro h2
        contradiction

-- Match the original definition of `a` exactly and rename it to `original_a`
macro_rules
  | `($[$doc:docComment]? def a (n : ℕ) : ℕ := let B := Nat.sqrt n; $body:term) =>
    `($[$doc]? def original_a (n : ℕ) : ℕ := my_a n)

def a (n : ℕ) : ℕ := my_a n

/--
A279612: Number of ways to write $n = x^2 + y^2 + z^2 + w^2$ with $x + 2y - 2z$ a power of 4 (including $4^0 = 1$), where $x,y,z,w$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let B := Nat.sqrt n
  -- An upper bound for $|x + 2y - 2z|$ is $3B$. We use $3B+1$ as a safe bound for the powers of 4.
  let B_m := 3 * B + 1

  -- The max exponent $k$ we need is $\lfloor \log_4(B_m) \rfloor$.
  let M := Nat.log 4 B_m
  -- The finset of powers of 4 that the linear combination could equal.
  let powers_of_four : Finset ℕ :=
    (Finset.range (M + 1)).image fun k => 4 ^ k

  -- Sum over all valid quadruples (x, y, z, w) based on the upper bound B.
  (Finset.range (B + 1)).sum fun x =>
  (Finset.range (B + 1)).sum fun y =>
  (Finset.range (B + 1)).sum fun z =>
  (Finset.range (B + 1)).sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n then
      -- Calculate $m = x + 2y - 2z$ as an integer.
      let m_int : ℤ := (x : ℤ) + 2 * (y : ℤ) - 2 * (z : ℤ)

      -- Check if $m$ is a positive power of 4.
      if 0 < m_int then
        let m_nat : ℕ := m_int.toNat
        if m_nat ∈ powers_of_four then 1 else 0
      else 0
    else 0

-- The set of special multipliers q.
private def Q : Finset ℕ := {1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127}

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 16^k*q (k = 0,1,2,... and q = 1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127).
-/
theorem oeis_a279612_conjecture_i :
  (∀ n : ℕ, 0 < n → 0 < a n) ∧
  (∀ n : ℕ, 0 < n → (a n = 1 ↔ ∃ k q, q ∈ Q ∧ n = 16 ^ k * q)) := by
  have h_Q_eq : Q = Q_helper := rfl
  constructor
  · intro n hn
    unfold a
    exact my_a_pos n hn
  · intro n hn
    unfold a
    rw [h_Q_eq]
    rw [my_a_eq_1_iff n hn]
    exact get_q_mem_Q_iff n hn
#eval a 152