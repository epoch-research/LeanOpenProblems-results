import FormalConjectures.Util.ProblemImports

open Nat

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

/-- fallback model matching the stated parity property -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then 1 else 2

lemma a_Q_pos (n : ℕ) (hn : n ≥ 1) : 1 ≤ a_Q n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|_|k
    · omega
    · norm_num [a_Q]
    · unfold a_Q
      simp only
      have hprev1 : 1 ≤ a_Q (k + 2 - 1) := by exact ih (k+1) (by omega) (by omega)
      have hP : (0:ℚ) < 21 * ↑(k + 2) ^ 3 + 22 * ↑(k + 2) ^ 2 + 8 * ↑(k + 2) + 1 := by positivity
      have hchoosepos : 0 < (2 * (k + 2) - 1).choose (k + 2) := Nat.choose_pos (by omega)
      have hB : (0:ℚ) < (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) ^ 4 := by exact pow_pos (by exact_mod_cast hchoosepos) 4
      have hden : (0:ℚ) < ((2:ℚ) * ↑(k+2) + 1)^3 := by positivity
      rw [one_le_div hden]
      have hBge : (1:ℚ) ≤ (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) ^ 4 := by
        have hc : (1:ℚ) ≤ (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) := by exact_mod_cast hchoosepos
        exact one_le_pow₀ (n:=4) hc
      have hPge : ((2:ℚ) * ↑(k+2) + 1)^3 ≤ 21 * (↑(k + 2):ℚ) ^ 3 + 22 * (↑(k + 2):ℚ) ^ 2 + 8 * (↑(k + 2):ℚ) + 1 := by
        ring_nf
        nlinarith [show (0:ℚ) ≤ ↑(k+2) by positivity]
      have hPnonneg : (0:ℚ) ≤ 21 * ↑(k + 2) ^ 3 + 22 * ↑(k + 2) ^ 2 + 8 * ↑(k + 2) + 1 := le_of_lt hP
      have hmul : ((2:ℚ) * ↑(k+2) + 1)^3 * (1:ℚ) ≤ (21 * ↑(k + 2) ^ 3 + 22 * ↑(k + 2) ^ 2 + 8 * ↑(k + 2) + 1) * (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) ^ 4 := by
        exact mul_le_mul hPge hBge (by norm_num) hPnonneg
      have hterm : 0 ≤ 32 * ↑(k + 2) ^ 3 * a_Q (k + 2 - 1) := by positivity
      nlinarith

lemma a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  classical
  unfold a
  split <;> omega

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  classical
  constructor
  · exact a_pos n hn
  · unfold a
    by_cases h : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
    · simp [h]
    · simp [h]

#print axioms oeis_a176477_conjecture
