import FormalConjectures.Util.ProblemImports

open Nat

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

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

theorem a16_val : a 16 = 21177399672884572861259940658608625 := by
  unfold a
  dsimp only [a_Q]
  have hc2 : choose 3 2 = 3 := rfl
  have hc3 : choose 5 3 = 10 := rfl
  have hc4 : choose 7 4 = 35 := rfl
  have hc5 : choose 9 5 = 126 := rfl
  have hc6 : choose 11 6 = 462 := rfl
  have hc7 : choose 13 7 = 1716 := rfl
  have hc8 : choose 15 8 = 6435 := rfl
  have hc9 : choose 17 9 = 24310 := rfl
  have hc10 : choose 19 10 = 92378 := rfl
  have hc11 : choose 21 11 = 352716 := rfl
  have hc12 : choose 23 12 = 1352078 := rfl
  have hc13 : choose 25 13 = 5200300 := rfl
  have hc14 : choose 27 14 = 20058300 := rfl
  have hc15 : choose 29 15 = 77558760 := rfl
  have hc16 : choose 31 16 = 300540195 := rfl
  rw [hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]
  norm_num
  rfl
