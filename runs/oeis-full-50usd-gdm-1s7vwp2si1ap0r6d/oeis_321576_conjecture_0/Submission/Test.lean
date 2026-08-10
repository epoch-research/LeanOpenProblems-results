import FormalConjectures.Util.ProblemImports

open Nat Set ZMod

lemma p_square_two_le_two_pow_sub_two (p : ℕ) (hp : p ≥ 7) : p * p * 2 ≤ 2 ^ p - 2 := by
  induction p, hp using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    have h1 : 2 ^ (x + 1) - 2 = 2 * (2 ^ x - 2) + 2 := by
      have : 2 ^ x ≥ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hx
      omega
    rw [h1]
    have h2 : 2 * (2 ^ x - 2) + 2 ≥ 2 * (x * x * 2) + 2 := by omega
    have h3 : 2 * (x * x * 2) + 2 ≥ (x + 1) * (x + 1) * 2 := by
      have h4 : (x + 1) * (x + 1) * 2 = 2 * (x * x) + 4 * x + 2 := by ring
      have h5 : 2 * (x * x * 2) + 2 = 4 * (x * x) + 2 := by ring
      rw [h4, h5]
      have h6 : 2 * (x * x) ≥ 4 * x := by
        have h7 : 2 * x ≥ 4 := by omega
        calc 2 * (x * x) = (2 * x) * x := by ring
        _ ≥ 4 * x := Nat.mul_le_mul_right x h7
      omega
    omega

