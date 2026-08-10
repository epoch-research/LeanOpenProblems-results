import FormalConjectures.Util.ProblemImports
open Nat
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
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat
example (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ, a_Q n = z := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|_|k
    · omega
    · exact ⟨2, by norm_num [a_Q]⟩
    · rcases ih (k+1) (by omega) (by omega) with ⟨z,hz⟩
      use ((32 * (k+2)^3 * z + (21*(k+2)^3+22*(k+2)^2+8*(k+2)+1) * ((2*(k+2)-1).choose (k+2))^4) / ((2*(k+2)+1)^3) : ℤ)
      rw [a_Q.eq_3]
      have hsub : k+2-1=k+1 := by omega
      rw [hsub,hz]
      norm_num
      ring_nf
      try omega
      try aesop
      try grind
      trace_state
      sorry
