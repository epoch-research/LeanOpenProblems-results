import Mathlib

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem test_eval_p5 : padicNorm 5 (25 : ℚ) = 1 / 25 := by
  rw [padicNorm.eq_zpow_of_nonzero (by norm_num)]
  change (5 : ℚ) ^ (- padicValRat 5 (25 : ℚ)) = 1 / 25
  have : padicValRat 5 (25 : ℚ) = 2 := by
    show padicValRat 5 (↑(25 : ℕ)) = 2
    rw [padicValRat.of_nat]
    change (padicValNat 5 (5 ^ 2) : ℤ) = 2
    rw [padicValNat.prime_pow]
    rfl
  rw [this]
  norm_num
