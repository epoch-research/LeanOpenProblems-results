import FormalConjectures.Util.ProblemImports

open Nat

-- let us first verify 2^j ≡ 1 [MOD 3] for even j
lemma even_pow_two_mod_three (j : ℕ) (hj : Even j) : 2^j % 3 = 1 := by
  rcases hj with ⟨m, rfl⟩
  rw [mul_comm]
  have h_pow : 2^(m * 2) = (2^2)^m := by
    rw [pow_mul]
  rw [h_pow]
  simp
  -- 4^m % 3 = 1
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have h_pow_succ : 4^(m+1) = 4^m * 4 := by ring
    rw [h_pow_succ]
    rw [Nat.mul_mod]
    rw [ih]
    simp

lemma odd_pow_two_mod_three (j : ℕ) (hj : Odd j) : 2^j % 3 = 2 := by
  rcases hj with ⟨m, rfl⟩
  -- 2^(2*m + 1) = 2^(2*m) * 2 = 4^m * 2
  have h_pow : 2^(2 * m + 1) = 2^(2 * m) * 2 := pow_succ' 2 (2 * m)
  have h_pow2 : 2^(2 * m) = (2^2)^m := pow_mul 2 2 m
  rw [h_pow, h_pow2]
  simp
  -- 4^m * 2 % 3 = 2
  have h_m_even : Even (2 * m) := by
    use m
    ring
  have h_mod := even_pow_two_mod_three (2 * m) h_m_even
  have h_pow_rw : (2^2)^m = 2^(2 * m) := (pow_mul 2 2 m).symm
  rw [h_pow_rw] at h_mod
  simp at h_mod
  rw [Nat.mul_mod]
  rw [h_mod]
  simp
