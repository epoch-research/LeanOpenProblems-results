import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

theorem a1_val : a 1 = 2 := rfl

theorem a2_val : a 2 = 181 := by
  unfold a
  dsimp only [a_Q]
  norm_num
  rfl

theorem a3_val : a 3 = 23488 := by
  unfold a
  dsimp only [a_Q]
  have h_choose : choose 5 3 = 10 := rfl
  rw [h_choose]
  norm_num
  rfl
