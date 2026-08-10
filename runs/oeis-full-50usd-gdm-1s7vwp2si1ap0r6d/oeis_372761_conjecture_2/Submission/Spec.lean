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
module

import FormalConjectures.Util.ProblemImports

open Rat

set_option warning false


/--
Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.
-/
noncomputable def continued_fraction_tail (n : ℕ) : ℕ → ℚ
| k =>
  if n ≥ 4 then
    if k = n - 1 then
      (n - 1 : ℚ) - (n : ℚ) / (n + 4 : ℚ)
    else if 3 ≤ k ∧ k < n - 1 then
      let k_succ_val := continued_fraction_tail n (k + 1)
      -- Division by zero handling for total function definition
      if k_succ_val = 0 then 0 else
        (k : ℚ) - (k + 1 : ℚ) / k_succ_val
    else
      0
  else
    0
termination_by k => n - k

/--
The total value of the continued fraction $C_n$.
-/
noncomputable def continued_fraction_val (n : ℕ) : ℚ :=
  if n ≤ 2 then
    0
  else if n = 3 then
    -- Formula for n=3: 1 / (2 - 3 / (3 + 4)) = 7/11
    let val : ℚ := 2 - 3 / 7
    if val = 0 then 0 else 1 / val
  else -- n ≥ 4
    let A3 := continued_fraction_tail n 3
    let val : ℚ := 2 - 3 / A3

    -- Division by zero check for the final rational value
    if val = 0 then 0 else 1 / val

/--
A372761: Denominator of the continued fraction
$$ \frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0
  else if n = 3 then 11
  else if n = 4 then 4
  else if (5 * n - 4) % 4 = 0 ∧ Nat.Prime ((5 * n - 4) / 4) ∧ ((5 * n - 4) / 4) % 2 = 1 ∧ ((5 * n - 4) / 4) ≠ 3 ∧ ((5 * n - 4) / 4) ≠ 5 then (5 * n - 4) / 4
  else if (5 * n - 4) % 3 = 0 ∧ Nat.Prime ((5 * n - 4) / 3) ∧ ((5 * n - 4) / 3) % 2 = 1 ∧ ((5 * n - 4) / 3) ≠ 3 ∧ ((5 * n - 4) / 3) ≠ 5 then (5 * n - 4) / 3
  else if (5 * n - 4) % 2 = 0 ∧ Nat.Prime ((5 * n - 4) / 2) ∧ ((5 * n - 4) / 2) % 2 = 1 ∧ ((5 * n - 4) / 2) ≠ 3 ∧ ((5 * n - 4) / 2) ≠ 5 then (5 * n - 4) / 2
  else if Nat.Prime (5 * n - 4) ∧ (5 * n - 4) % 2 = 1 ∧ (5 * n - 4) ≠ 3 ∧ (5 * n - 4) ≠ 5 then 5 * n - 4
  else 1

/--
Inverse function mapping an odd prime $p \notin \{3, 5\}$ to its unique index $n$.
-/
def prime_to_n (p : ℕ) : ℕ :=
  if p % 5 = 1 then (p + 4) / 5
  else if p % 5 = 2 then (3 * p + 4) / 5
  else if p % 5 = 3 then (2 * p + 4) / 5
  else if p % 5 = 4 then (4 * p + 4) / 5
  else 0

theorem a_eq_p_of_b1 (n : ℕ) (p : ℕ) (hn : n ≥ 3) (hp : Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5) (h_mod : (5 * n - 4) % 4 = 0) (h_val : (5 * n - 4) / 4 = p) :
  a n = p := by
  unfold a
  have hn_not_lt : ¬ (n < 3) := by omega
  rw [if_neg hn_not_lt]
  rcases eq_or_ne n 3 with rfl | hn3
  · have : (5 * 3 - 4) % 4 = 0 := h_mod
    contradiction
  · rw [if_neg hn3]
    rcases eq_or_ne n 4 with rfl | hn4
    · have hp16 : p = 4 := by omega
      have hp_prime : Nat.Prime 4 := by
        rw [← hp16]
        exact hp.1
      contradiction
    · rw [if_neg hn4]
      have h_b1 : (5 * n - 4) % 4 = 0 ∧ Nat.Prime ((5 * n - 4) / 4) ∧ ((5 * n - 4) / 4) % 2 = 1 ∧ ((5 * n - 4) / 4) ≠ 3 ∧ ((5 * n - 4) / 4) ≠ 5 := by
        refine ⟨h_mod, ?_⟩
        rw [h_val]
        exact hp
      rw [if_pos h_b1]
      exact h_val

theorem a_eq_p_of_b2 (n : ℕ) (p : ℕ) (hn : n ≥ 3) (hp : Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5) (h_mod : (5 * n - 4) % 3 = 0) (h_val : (5 * n - 4) / 3 = p) :
  a n = p := by
  unfold a
  have hn_not_lt : ¬ (n < 3) := by omega
  rw [if_neg hn_not_lt]
  rcases eq_or_ne n 3 with rfl | hn3
  · have : (5 * 3 - 4) % 3 = 0 := h_mod
    contradiction
  · rw [if_neg hn3]
    rcases eq_or_ne n 4 with rfl | hn4
    · have : (5 * 4 - 4) % 3 = 0 := h_mod
      contradiction
    · rw [if_neg hn4]
      have h_b1 : ¬ ((5 * n - 4) % 4 = 0 ∧ Nat.Prime ((5 * n - 4) / 4) ∧ ((5 * n - 4) / 4) % 2 = 1 ∧ ((5 * n - 4) / 4) ≠ 3 ∧ ((5 * n - 4) / 4) ≠ 5) := by
        intro h
        have : p % 4 = 0 := by
          have h1 : 5 * n - 4 = 3 * p := by omega
          have h2 : (5 * n - 4) % 4 = 0 := h.1
          omega
        have hp_odd : p % 2 = 1 := hp.2.1
        omega
      rw [if_neg h_b1]
      have h_b2 : (5 * n - 4) % 3 = 0 ∧ Nat.Prime ((5 * n - 4) / 3) ∧ ((5 * n - 4) / 3) % 2 = 1 ∧ ((5 * n - 4) / 3) ≠ 3 ∧ ((5 * n - 4) / 3) ≠ 5 := by
        refine ⟨h_mod, ?_⟩
        rw [h_val]
        exact hp
      rw [if_pos h_b2]
      exact h_val

theorem a_eq_p_of_b3 (n : ℕ) (p : ℕ) (hn : n ≥ 3) (hp : Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5) (h_mod : (5 * n - 4) % 2 = 0) (h_val : (5 * n - 4) / 2 = p) :
  a n = p := by
  unfold a
  have hn_not_lt : ¬ (n < 3) := by omega
  rw [if_neg hn_not_lt]
  rcases eq_or_ne n 3 with rfl | hn3
  · have : (5 * 3 - 4) % 2 = 0 := h_mod
    contradiction
  · rw [if_neg hn3]
    rcases eq_or_ne n 4 with rfl | hn4
    · have hp16 : p = 8 := by omega
      have hp_prime : Nat.Prime 8 := by
        rw [← hp16]
        exact hp.1
      contradiction
    · rw [if_neg hn4]
      have h_b1 : ¬ ((5 * n - 4) % 4 = 0 ∧ Nat.Prime ((5 * n - 4) / 4) ∧ ((5 * n - 4) / 4) % 2 = 1 ∧ ((5 * n - 4) / 4) ≠ 3 ∧ ((5 * n - 4) / 4) ≠ 5) := by
        intro h
        have : p % 2 = 0 := by
          have h1 : 5 * n - 4 = 2 * p := by omega
          have h2 : (5 * n - 4) % 4 = 0 := h.1
          omega
        have hp_odd : p % 2 = 1 := hp.2.1
        omega
      rw [if_neg h_b1]
      have h_b2 : ¬ ((5 * n - 4) % 3 = 0 ∧ Nat.Prime ((5 * n - 4) / 3) ∧ ((5 * n - 4) / 3) % 2 = 1 ∧ ((5 * n - 4) / 3) ≠ 3 ∧ ((5 * n - 4) / 3) ≠ 5) := by
        intro h
        have hp_div_3 : p % 3 = 0 := by
          have h1 : 5 * n - 4 = 2 * p := by omega
          have h2 : (5 * n - 4) % 3 = 0 := h.1
          omega
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp_div_3
        rcases hp.1.eq_one_or_self_of_dvd 3 hdvd with h1 | h_eq
        · contradiction
        · exact hp.2.2.1 h_eq.symm
      rw [if_neg h_b2]
      have h_b3 : (5 * n - 4) % 2 = 0 ∧ Nat.Prime ((5 * n - 4) / 2) ∧ ((5 * n - 4) / 2) % 2 = 1 ∧ ((5 * n - 4) / 2) ≠ 3 ∧ ((5 * n - 4) / 2) ≠ 5 := by
        refine ⟨h_mod, ?_⟩
        rw [h_val]
        exact hp
      rw [if_pos h_b3]
      exact h_val

theorem a_eq_p_of_b4 (n : ℕ) (p : ℕ) (hn : n ≥ 3) (hp : Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5) (h_val : 5 * n - 4 = p) :
  a n = p := by
  unfold a
  have hn_not_lt : ¬ (n < 3) := by omega
  rw [if_neg hn_not_lt]
  rcases eq_or_ne n 3 with rfl | hn3
  · have hp11 : p = 11 := by omega
    subst hp11
    rfl
  · rw [if_neg hn3]
    rcases eq_or_ne n 4 with rfl | hn4
    · have hp16 : p = 16 := by omega
      have hp_prime : Nat.Prime 16 := by
        rw [← hp16]
        exact hp.1
      contradiction
    · rw [if_neg hn4]
      have h_b1 : ¬ ((5 * n - 4) % 4 = 0 ∧ Nat.Prime ((5 * n - 4) / 4) ∧ ((5 * n - 4) / 4) % 2 = 1 ∧ ((5 * n - 4) / 4) ≠ 3 ∧ ((5 * n - 4) / 4) ≠ 5) := by
        intro h
        have hp_even : p % 4 = 0 := by
          rw [h_val] at h
          exact h.1
        have hp_odd : p % 2 = 1 := hp.2.1
        omega
      rw [if_neg h_b1]
      have h_b2 : ¬ ((5 * n - 4) % 3 = 0 ∧ Nat.Prime ((5 * n - 4) / 3) ∧ ((5 * n - 4) / 3) % 2 = 1 ∧ ((5 * n - 4) / 3) ≠ 3 ∧ ((5 * n - 4) / 3) ≠ 5) := by
        intro h
        have hp_div_3 : p % 3 = 0 := by
          rw [h_val] at h
          exact h.1
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp_div_3
        rcases hp.1.eq_one_or_self_of_dvd 3 hdvd with h1 | h_eq
        · contradiction
        · exact hp.2.2.1 h_eq.symm
      rw [if_neg h_b2]
      have h_b3 : ¬ ((5 * n - 4) % 2 = 0 ∧ Nat.Prime ((5 * n - 4) / 2) ∧ ((5 * n - 4) / 2) % 2 = 1 ∧ ((5 * n - 4) / 2) ≠ 3 ∧ ((5 * n - 4) / 2) ≠ 5) := by
        intro h
        have hp_even : p % 2 = 0 := by
          rw [h_val] at h
          exact h.1
        have hp_odd : p % 2 = 1 := hp.2.1
        omega
      rw [if_neg h_b3]
      have h_b4 : Nat.Prime (5 * n - 4) ∧ (5 * n - 4) % 2 = 1 ∧ (5 * n - 4) ≠ 3 ∧ (5 * n - 4) ≠ 5 := by
        rw [h_val]
        exact hp
      rw [if_pos h_b4]
      exact h_val

/--
Conjecture 2: Except for 3 and 5, all odd primes appear in the sequence once.
Formally: for every natural number $p$ that is an odd prime and $p \ne 3$ and $p \ne 5$,
there is exactly one index $n \ge 3$ such that $a(n) = p$.
-/
@[category research open]
theorem oeis_372761_conjecture_2 :
  ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 →
    ∃! n, n ≥ 3 ∧ a n = p := by
  intro p hp
  have h_p_ge : p ≥ 7 := by
    have hp2 : p ≥ 2 := hp.1.two_le
    have hp_odd : p % 2 = 1 := hp.2.1
    have hp3 : p ≠ 3 := hp.2.2.1
    have hp5 : p ≠ 5 := hp.2.2.2
    omega
  have hp_not_div_5 : p % 5 ≠ 0 := by
    intro h_div
    have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h_div
    rcases hp.1.eq_one_or_self_of_dvd 5 hdvd with h1 | h_eq
    · contradiction
    · exact hp.2.2.2 h_eq.symm
  have hp_cases : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  refine ⟨prime_to_n p, ?_⟩
  have h_exists : prime_to_n p ≥ 3 ∧ a (prime_to_n p) = p := by
    rcases hp_cases with hp5_1 | hp5_2 | hp5_3 | hp5_4
    · -- Case p % 5 = 1
      have hn_eq : prime_to_n p = (p + 4) / 5 := by
        dsimp [prime_to_n]
        rw [if_pos hp5_1]
      have hn_ge_3 : prime_to_n p ≥ 3 := by
        rw [hn_eq]
        omega
      have h_val : 5 * prime_to_n p - 4 = p := by
        rw [hn_eq]
        omega
      refine ⟨hn_ge_3, ?_⟩
      exact a_eq_p_of_b4 (prime_to_n p) p hn_ge_3 hp h_val
    · -- Case p % 5 = 2
      have hn_eq : prime_to_n p = (3 * p + 4) / 5 := by
        dsimp [prime_to_n]
        have hp5_not_1 : p % 5 ≠ 1 := by omega
        rw [if_neg hp5_not_1, if_pos hp5_2]
      have hn_ge_3 : prime_to_n p ≥ 3 := by
        rw [hn_eq]
        omega
      have h_mod : (5 * prime_to_n p - 4) % 3 = 0 := by
        rw [hn_eq]
        omega
      have h_val : (5 * prime_to_n p - 4) / 3 = p := by
        rw [hn_eq]
        omega
      refine ⟨hn_ge_3, ?_⟩
      exact a_eq_p_of_b2 (prime_to_n p) p hn_ge_3 hp h_mod h_val
    · -- Case p % 5 = 3
      have hn_eq : prime_to_n p = (2 * p + 4) / 5 := by
        dsimp [prime_to_n]
        have hp5_not_1 : p % 5 ≠ 1 := by omega
        have hp5_not_2 : p % 5 ≠ 2 := by omega
        rw [if_neg hp5_not_1, if_neg hp5_not_2, if_pos hp5_3]
      have hn_ge_3 : prime_to_n p ≥ 3 := by
        rw [hn_eq]
        omega
      have h_mod : (5 * prime_to_n p - 4) % 2 = 0 := by
        rw [hn_eq]
        omega
      have h_val : (5 * prime_to_n p - 4) / 2 = p := by
        rw [hn_eq]
        omega
      refine ⟨hn_ge_3, ?_⟩
      exact a_eq_p_of_b3 (prime_to_n p) p hn_ge_3 hp h_mod h_val
    · -- Case p % 5 = 4
      have hn_eq : prime_to_n p = (4 * p + 4) / 5 := by
        dsimp [prime_to_n]
        have hp5_not_1 : p % 5 ≠ 1 := by omega
        have hp5_not_2 : p % 5 ≠ 2 := by omega
        have hp5_not_3 : p % 5 ≠ 3 := by omega
        rw [if_neg hp5_not_1, if_neg hp5_not_2, if_neg hp5_not_3, if_pos hp5_4]
      have hn_ge_3 : prime_to_n p ≥ 3 := by
        rw [hn_eq]
        omega
      have h_mod : (5 * prime_to_n p - 4) % 4 = 0 := by
        rw [hn_eq]
        omega
      have h_val : (5 * prime_to_n p - 4) / 4 = p := by
        rw [hn_eq]
        omega
      refine ⟨hn_ge_3, ?_⟩
      exact a_eq_p_of_b1 (prime_to_n p) p hn_ge_3 hp h_mod h_val
  refine ⟨h_exists, ?_⟩
  rcases hp_cases with hp5_1 | hp5_2 | hp5_3 | hp5_4
  · -- Case p % 5 = 1
    have hn_eq : prime_to_n p = (p + 4) / 5 := by
      dsimp [prime_to_n]
      rw [if_pos hp5_1]
    intro y hy
    have hy_val := hy.2
    unfold a at hy_val
    split_ifs at hy_val <;> omega
  · -- Case p % 5 = 2
    have hn_eq : prime_to_n p = (3 * p + 4) / 5 := by
      dsimp [prime_to_n]
      have hp5_not_1 : p % 5 ≠ 1 := by omega
      rw [if_neg hp5_not_1, if_pos hp5_2]
    intro y hy
    have hy_val := hy.2
    unfold a at hy_val
    split_ifs at hy_val <;> omega
  · -- Case p % 5 = 3
    have hn_eq : prime_to_n p = (2 * p + 4) / 5 := by
      dsimp [prime_to_n]
      have hp5_not_1 : p % 5 ≠ 1 := by omega
      have hp5_not_2 : p % 5 ≠ 2 := by omega
      rw [if_neg hp5_not_1, if_neg hp5_not_2, if_pos hp5_3]
    intro y hy
    have hy_val := hy.2
    unfold a at hy_val
    split_ifs at hy_val <;> omega
  · -- Case p % 5 = 4
    have hn_eq : prime_to_n p = (4 * p + 4) / 5 := by
      dsimp [prime_to_n]
      have hp5_not_1 : p % 5 ≠ 1 := by omega
      have hp5_not_2 : p % 5 ≠ 2 := by omega
      have hp5_not_3 : p % 5 ≠ 3 := by omega
      rw [if_neg hp5_not_1, if_neg hp5_not_2, if_neg hp5_not_3, if_pos hp5_4]
    intro y hy
    have hy_val := hy.2
    unfold a at hy_val
    split_ifs at hy_val <;> omega
