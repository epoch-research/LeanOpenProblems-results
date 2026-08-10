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

opaque a_Q_int (n : ℕ) : ∃ z : ℤ, a_Q n = (z : ℚ)



#print axioms test_opaque









