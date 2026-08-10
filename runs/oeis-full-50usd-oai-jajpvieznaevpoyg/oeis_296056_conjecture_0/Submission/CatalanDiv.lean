import FormalConjectures.Util.ProblemImports
open Nat

lemma catalan_div3_identity_q (n : ℕ) (hn : n ≠ 0) :
    (3 * (catalan (2*n-2) : ℚ) / (n:ℚ)) =
      ((Nat.choose (4*n-1) (2*n-1) : ℕ) : ℚ) - 8 * ((Nat.choose (4*n-4) (2*n-3) : ℕ) : ℚ) := by
  have hnq : (n:ℚ) ≠ 0 := by exact_mod_cast hn
  rw [catalan_eq_centralBinom_div]
  rw [Nat.centralBinom_eq_two_mul_choose]
  -- after rewrites, all choose; try factorial formula
  rw [Nat.cast_div]
  · rw [Nat.cast_choose, Nat.cast_choose, Nat.cast_choose]
    rw [show 2 * (2*n-2) = 4*n-4 by omega]
    -- try norm_num? 
    field_simp [hnq]
    -- stuck choose
    sorry
  · exact Nat.succ_dvd_centralBinom _
  · norm_num

#check Nat.choose_eq_factorial_div_factorial
#check Nat.choose_mul_factorial_mul_factorial
