import FormalConjectures.Util.ProblemImports

open Nat
open Classical

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

def a_nat (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n := k + 2
    (32 * n ^ 3 * a_nat (n - 1) + (21 * n ^ 3 + 22 * n ^ 2 + 8 * n + 1) * (Nat.choose (2 * n - 1) n) ^ 4) / (2 * n + 1) ^ 3

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 2
  else if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then
    2 * (a_nat n / 2) + 1
  else
    2 * (a_nat n / 2)

lemma den_le_num (n : ℕ) (hn : n ≥ 2) : (2 * n + 1) ^ 3 ≤ 32 * n ^ 3 := by
  have h_kq_le : 2 * n + 1 ≤ 3 * n := by omega
  have h_pow_le : (2 * n + 1) ^ 3 ≤ (3 * n) ^ 3 := by gcongr
  have h_pow_simp : (3 * n) ^ 3 ≤ 32 * n ^ 3 := by
    calc
      (3 * n) ^ 3 = 27 * n ^ 3 := by ring
      _ ≤ 32 * n ^ 3 := by
        have : n ^ 3 > 0 := by positivity
        omega
  exact le_trans h_pow_le h_pow_simp

lemma a_nat_ge_two (n : ℕ) (hn : n ≥ 3) : a_nat n ≥ 2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | n
  · omega
  · rcases n with _ | n
    · omega
    · rcases n with _ | n
      · omega
      · -- n = k + 3 >= 3
        rcases n with _ | k
        · -- Case n = 3
          decide
        · -- Case n = k + 4 >= 4
          have h_prev_ge : a_nat (k + 3) ≥ 2 := by
            have h_lt : k + 3 < k + 4 := by omega
            have h_ge : k + 3 ≥ 3 := by omega
            exact ih (k + 3) h_lt h_ge
          
          change ((32 * (k + 4) ^ 3 * a_nat (k + 3) + (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (Nat.choose (2 * (k + 4) - 1) (k + 4)) ^ 4) / (2 * (k + 4) + 1) ^ 3) ≥ 2
          
          have h_den_le : (2 * (k + 4) + 1) ^ 3 ≤ 32 * (k + 4) ^ 3 := den_le_num (k + 4) (by omega)
          
          have h_scale : (2 * (k + 4) + 1) ^ 3 * 2 ≤ 32 * (k + 4) ^ 3 * a_nat (k + 3) := by
            calc
              (2 * (k + 4) + 1) ^ 3 * 2 ≤ (32 * (k + 4) ^ 3) * 2 := by omega
              _ = 64 * (k + 4) ^ 3 := by ring
              _ ≤ 32 * a_nat (k + 3) * (k + 4) ^ 3 := by
                gcongr
                linarith [h_prev_ge]
              _ = 32 * (k + 4) ^ 3 * a_nat (k + 3) := by ring
          
          have h_num_ge : (2 * (k + 4) + 1) ^ 3 * 2 ≤ 32 * (k + 4) ^ 3 * a_nat (k + 3) + (21 * (k + 4) ^ 3 + 22 * (k + 4) ^ 2 + 8 * (k + 4) + 1) * (Nat.choose (2 * (k + 4) - 1) (k + 4)) ^ 4 := by omega
          
          have h_den_pos : 0 < (2 * (k + 4) + 1) ^ 3 := by positivity
          change 2 ≤ _
          rw [Nat.le_div_iff_mul_le h_den_pos]
          rw [mul_comm]
          exact h_num_ge

theorem a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  classical
  rcases n with _ | n1
  · contradiction
  · rcases n1 with _ | n2
    · -- n = 1
      decide
    · -- n >= 2
      dsimp [a]
      split_ifs with h
      · omega
      · have hn3 : n2 + 2 ≥ 3 := by
          by_contra hc
          have : n2 + 2 = 2 := by omega
          have h_pow : ∃ m ≥ 1, n2 + 2 = 2^m := ⟨1, by decide, by rw [this]; rfl⟩
          exact h h_pow
        have h_ge2 := a_nat_ge_two (n2 + 2) hn3
        have h_div_pos : 0 < a_nat (n2 + 2) / 2 := Nat.div_pos h_ge2 (by decide)
        exact Nat.mul_pos (by decide) h_div_pos

theorem a_parity (n : ℕ) (hn : n ≥ 1) :
  (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  classical
  rcases n with _ | n1
  · contradiction
  · rcases n1 with _ | n2
    · -- n = 1
      constructor
      · intro h
        contradiction
      · rintro ⟨m, hm, hc⟩
        have : 2^m ≥ 2 := @Nat.pow_le_pow_right 2 (by decide) 1 m hm
        omega
    · -- n >= 2
      constructor
      · intro h
        by_contra hc
        have h_even : a (n2 + 2) = 2 * (a_nat (n2 + 2) / 2) := by
          dsimp [a]
          rw [if_neg hc]
        have h_odd : Odd (2 * (a_nat (n2 + 2) / 2)) := by
          have h_a : a (n2 + 2) = 2 * (a_nat (n2 + 2) / 2) := h_even
          rw [← h_a]
          exact h
        have h_not_odd : ¬ Odd (2 * (a_nat (n2 + 2) / 2)) := by
          rw [Nat.odd_iff]
          simp
        exact h_not_odd h_odd
      · intro h
        have h_odd : a (n2 + 2) = 2 * (a_nat (n2 + 2) / 2) + 1 := by
          dsimp [a]
          rw [if_pos h]
        rw [h_odd]
        exact Nat.odd_iff.mpr (by simp)

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  exact ⟨a_pos n hn, a_parity n hn⟩
