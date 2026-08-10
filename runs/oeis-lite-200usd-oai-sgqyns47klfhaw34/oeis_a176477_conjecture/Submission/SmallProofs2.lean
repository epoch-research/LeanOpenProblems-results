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
example : a 1 = 2 := by
  unfold a; norm_num [a_Q]; rw [Rat.floor_intCast]; norm_num
example : ¬ Odd (a 1) := by
  rw [show a 1 = 2 by unfold a; norm_num [a_Q]; rw [Rat.floor_intCast]; norm_num]
  norm_num [Odd]
example : ¬ (∃ m : ℕ, m ≥ 1 ∧ 1 = 2^m) := by
  rintro ⟨m, hm, h⟩
  cases m with
  | zero => omega
  | succ k =>
    have hpow : 2^k ≥ 1 := Nat.one_le_pow k (by norm_num)
    rw [pow_succ'] at h
    omega
example : a 2 = 181 := by
  unfold a; norm_num [a_Q]; rw [Rat.floor_intCast]; norm_num
example : Odd (a 2) := by
  rw [show a 2 = 181 by unfold a; norm_num [a_Q]; rw [Rat.floor_intCast]; norm_num]
  norm_num [Odd]
