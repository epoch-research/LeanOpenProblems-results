import Mathlib

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  change (n + 1).choose (1 + 1) = _
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

lemma choose_two_add (p : ℕ) : p.choose 2 + p.choose 2 = p * (p - 1) := by
  cases p with
  | zero => rfl
  | succ p =>
    induction p with
    | zero => rfl
    | succ p ih =>
      have H1 : (p + 2).choose 2 = (p + 1).choose 2 + (p + 1) := by
        change (p + 1 + 1).choose (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [H1]
      have H2 : (p + 1).choose 2 + (p + 1) + ((p + 1).choose 2 + (p + 1)) =
        ((p + 1).choose 2 + (p + 1).choose 2) + 2 * (p + 1) := by omega
      rw [H2, ih]
      have H4 : p + 1 - 1 = p := rfl
      rw [H4]
      have H5 : p + 1 + 1 - 1 = p + 1 := rfl
      rw [H5]
      ring

lemma choose_add_gen (x y : ℕ) : (x + y).choose 2 = x.choose 2 + y.choose 2 + x * y := by
  induction y with
  | zero =>
    have : (0 : ℕ).choose 2 = 0 := rfl
    rw [this, Nat.add_zero, add_zero, mul_zero, add_zero]
  | succ y ih =>
    have h1 : x + (y + 1) = (x + y) + 1 := by omega
    rw [h1, choose_two_succ, ih]
    have h2 : (y + 1).choose 2 = y.choose 2 + y := choose_two_succ y
    rw [h2]
    have h3 : x * (y + 1) = x * y + x := by ring
    rw [h3]
    omega

lemma choose_two_mul_two (p : ℕ) (hp : p > 2) : (2 * (p - 1)).choose 2 = (p - 1) * (2 * p - 3) := by
  have H := choose_add_gen (p - 1) (p - 1)
  have H2 : p - 1 + (p - 1) = 2 * (p - 1) := by omega
  rw [H2] at H
  rw [H]
  have H3 : (p - 1).choose 2 + (p - 1).choose 2 = (p - 1) * (p - 2) := by
    have : p - 2 = (p - 1) - 1 := by omega
    rw [this, choose_two_add]
  rw [H3]
  zify [show 2 ≤ p by omega, show 3 ≤ 2 * p by omega]
  have hp_cast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  rw [hp_cast]
  ring

lemma two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p > 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : (p : ℤ) ∣ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h
  have h3 : (p : ℤ) ≤ 2 := by apply Int.le_of_dvd (by decide) h2
  omega

lemma pow_choose_add_two (p k : ℕ) [hp : Fact p.Prime] (hp2 : p > 2) :
    (2 : ZMod p) ^ (k + 1 + 2 * (p - 1)).choose 2 = (2 : ZMod p) ^ (k + 1).choose 2 := by
  rw [choose_add_gen, pow_add, pow_add]
  have H1 : (2 : ZMod p) ^ (2 * (p - 1)).choose 2 = 1 := by
    rw [choose_two_mul_two p hp2, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2), one_pow]
  rw [H1, mul_one]
  have h_comm2 : (k + 1) * (2 * (p - 1)) = (p - 1) * (2 * (k + 1)) := by ring
  have H2 : (2 : ZMod p) ^ ((k + 1) * (2 * (p - 1))) = 1 := by
    rw [h_comm2, pow_mul, ZMod.pow_card_sub_one_eq_one (two_ne_zero_zmod hp2), one_pow]
  rw [H2, mul_one]
