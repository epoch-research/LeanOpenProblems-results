import FormalConjectures.Util.ProblemImports

open Nat

def a_Q_rec (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    let a_prev : ℚ := a_Q_rec (n_idx - 1)
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4
    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3
    numerator / denominator

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

theorem a_Q_eq_rec (n : ℕ) : a_Q n = a_Q_rec n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · rfl
    rcases n with _|k
    · rfl
    · have h1 : k + 1 < k + 2 := Nat.lt_succ_self (k + 1)
      have ih1 := ih (k + 1) h1
      unfold a_Q a_Q_rec
      dsimp only
      have h_sub : k + 2 - 1 = k + 1 := rfl
      rw [h_sub]
      rw [ih1]

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

example : a 2 = 181 := by
  unfold a
  rw [a_Q_eq_rec]
  unfold a_Q_rec
  dsimp only
  unfold a_Q_rec
  norm_num
  change (Rat.floor ((181 : ℤ) : ℚ)).toNat = 181
  rw [Rat.floor_intCast]
  rfl
example : Odd (a 18) ↔ Odd (choose 17 9) := by
  unfold a
  rw [a_Q_eq_rec]
  decide

#eval a_Q_rec 2