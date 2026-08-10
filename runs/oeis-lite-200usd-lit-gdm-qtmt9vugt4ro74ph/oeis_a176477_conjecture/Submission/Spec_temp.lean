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


theorem a_Q_ge_two (n : ℕ) (hn : n ≥ 1) : a_Q n ≥ 2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · omega
  · rfl
  · unfold a_Q
    dsimp only
    have h_lt : k + 1 < k + 2 := by omega
    have h_ge1 : k + 1 ≥ 1 := by omega
    have h_prev := ih (k + 1) h_lt h_ge1
    have h_den_pos : 0 < (2 * (↑(k + 2) : ℚ) + 1) ^ 3 := by positivity
    rw [ge_iff_le]
    rw [le_div_iff₀ h_den_pos]
    have h_prev' : a_Q (k + 2 - 1) ≥ 2 := h_prev
    have h_term2_pos : (21 * (↑(k + 2) : ℚ) ^ 3 + 22 * (↑(k + 2) : ℚ) ^ 2 + 8 * (↑(k + 2) : ℚ) + 1) * (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) ^ 4 ≥ 0 := by positivity
    have h_x_nat : k + 2 ≥ 2 := by omega
    have h_x : (↑(k + 2) : ℚ) ≥ 2 := by exact_mod_cast h_x_nat
    have h_pow2 : (↑(k + 2) : ℚ) ^ 2 = (↑(k + 2) : ℚ) * (↑(k + 2) : ℚ) := by ring
    have h_pow3 : (↑(k + 2) : ℚ) ^ 3 = (↑(k + 2) : ℚ) * (↑(k + 2) : ℚ) ^ 2 := by ring
    have h_x_pow2 : (↑(k + 2) : ℚ) ^ 2 ≥ 0 := by positivity
    have h1 : 24 * (↑(k + 2) : ℚ) ^ 2 ≤ 12 * (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h2_a : 12 * (↑(k + 2) : ℚ) ≤ 6 * (↑(k + 2) : ℚ) ^ 2 := by nlinarith
    have h2_b : 6 * (↑(k + 2) : ℚ) ^ 2 ≤ 3 * (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h2 : 12 * (↑(k + 2) : ℚ) ≤ 3 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h3_a : (2 : ℚ) ≤ 4 * (↑(k + 2) : ℚ) := by linarith
    have h3_b : 4 * (↑(k + 2) : ℚ) ≤ 2 * (↑(k + 2) : ℚ) ^ 2 := by nlinarith
    have h3_c : 2 * (↑(k + 2) : ℚ) ^ 2 ≤ (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h3 : (2 : ℚ) ≤ (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_expand : 2 * (2 * (↑(k + 2) : ℚ) + 1) ^ 3 = 16 * (↑(k + 2) : ℚ) ^ 3 + 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 := by ring
    have h_sum : 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 ≤ 16 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_sum2 : 16 * (↑(k + 2) : ℚ) ^ 3 + 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 ≤ 32 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_cube_pos : 32 * (↑(k + 2) : ℚ) ^ 3 ≥ 0 := by positivity
    have h_mult : 32 * (↑(k + 2) : ℚ) ^ 3 * 2 ≤ 32 * (↑(k + 2) : ℚ) ^ 3 * a_Q (k + 2 - 1) := by nlinarith
    linarith


theorem a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  have h1 := a_Q_ge_two n hn
  unfold a
  have h2 : (2 : ℤ) ≤ (a_Q n).floor := Int.le_floor.mpr h1
  generalize h_x : (a_Q n).floor = x
  rw [h_x] at h2
  omega


/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n hn
  · sorry
