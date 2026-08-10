import FormalConjectures.Util.ProblemImports

open Nat

lemma even_pow_two_mod_three (j : ℕ) (hj : Even j) : 2^j % 3 = 1 := by
  rcases hj with ⟨m, rfl⟩
  have h_rw : m + m = 2 * m := by omega
  rw [h_rw]
  have h_pow : 2^(2 * m) = (2^2)^m := by
    rw [pow_mul]
  rw [h_pow]
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    have h_pow_succ : 4^(m+1) = 4^m * 4 := by ring
    rw [h_pow_succ]
    rw [Nat.mul_mod]
    rw [ih]
    rfl

lemma odd_pow_two_mod_three (j : ℕ) (hj : Odd j) : 2^j % 3 = 2 := by
  rcases hj with ⟨m, rfl⟩
  have h_pow : 2^(2 * m + 1) = 2^(2 * m) * 2 := by
    rw [pow_succ]
    ring
  rw [h_pow]
  have h_even : Even (2 * m) := by
    use m
    omega
  have h_mod := even_pow_two_mod_three (2 * m) h_even
  rw [Nat.mul_mod]
  rw [h_mod]
  rfl
