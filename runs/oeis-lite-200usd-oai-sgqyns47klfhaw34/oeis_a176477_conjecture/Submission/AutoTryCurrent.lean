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

example (n : ℕ) (hn : n ≥ 1) : a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|_|k
    · omega
    · constructor
      · unfold a; norm_num [a_Q]; rw [Rat.floor_intCast]; norm_num
      · constructor
        · intro ho; norm_num [a, a_Q, Odd] at ho
        · rintro ⟨m, hm, hpow⟩
          cases m with
          | zero => omega
          | succ mm =>
            rw [pow_succ'] at hpow
            have : 1 ≤ 2^mm := Nat.one_le_pow mm (by norm_num)
            omega
    · constructor
      · unfold a
        have hp : 1 ≤ a_Q (k+2) := by
          -- try positivity induction
          sorry
        sorry
      · grind
