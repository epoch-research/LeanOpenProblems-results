import FormalConjectures.Util.ProblemImports

open Nat

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

/--
A176477: $a(1)=2$; for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$
The sequence terms are non-negative integers. We compute the result using the rational recurrence and cast the result to $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

lemma a_Q_nonneg (n : ℕ) : 0 ≤ a_Q n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [a_Q]
    | succ n =>
      cases n with
      | zero => norm_num [a_Q]
      | succ k =>
        simp only [a_Q]
        apply div_nonneg
        · apply add_nonneg
          · have hprev : 0 ≤ a_Q (k + 1) := ih (k+1) (by omega)
            positivity
          · positivity
        · positivity

lemma a_Q_ge_one (n : ℕ) (hn : 1 ≤ n) : (1 : ℚ) ≤ a_Q n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => norm_num [a_Q]
      | succ k =>
        simp only [a_Q]
        have hprev : 0 ≤ a_Q (k + 2 - 1) := a_Q_nonneg _
        have hchoose_pos : 0 < Nat.choose (2 * (k + 2) - 1) (k + 2) := by
          apply Nat.choose_pos
          omega
        have hbin : (1 : ℚ) ≤ ((Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4) := by
          have hc : (1 : ℚ) ≤ (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) := by
            exact_mod_cast hchoose_pos
          nlinarith [sq_nonneg ((Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ)^2 - 1)]
        have hdenpos : (0 : ℚ) < (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 := by positivity
        rw [le_div_iff₀ hdenpos]
        have hgoal : (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 ≤
            32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 2 - 1) +
              (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1) *
                ↑((2 * (k + 2) - 1).choose (k + 2)) ^ 4 := by
          have hk : (0 : ℚ) ≤ ((k + 2 : ℕ) : ℚ) := by positivity
          have hP : (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 ≤
              21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1 := by
            ring_nf
            have hx : (0 : ℚ) ≤ ((k + 2 : ℕ) : ℚ) := by positivity
            have hx2 : (0 : ℚ) ≤ (((k + 2 : ℕ) : ℚ) ^ 2) := sq_nonneg _
            have hx3 : (0 : ℚ) ≤ (((k + 2 : ℕ) : ℚ) ^ 3) := by positivity
            nlinarith
          have hterm1 : 0 ≤ 32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 2 - 1) := by positivity
          nlinarith
        simpa using hgoal

lemma a_pos (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  rw [a]
  have hq : (1 : ℚ) ≤ a_Q n := a_Q_ge_one n hn
  have hf : (1 : ℤ) ≤ Rat.floor (a_Q n) := by
    exact Rat.le_floor_iff.mpr hq
  have hto : 0 < (Rat.floor (a_Q n)).toNat := by omega
  exact hto



/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  sorry
