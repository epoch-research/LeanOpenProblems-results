import FormalConjecturesUtil

/-! Real algebra bounds for a product of two perturbed means. -/
namespace Erdos972MeanProductErrorAlgebra

lemma product_difference_square_le {a b c d A B E F : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hc : c^2 ≤ A) (hb : b^2 ≤ B) (he : (a-c)^2 ≤ E) (hf : (b-d)^2 ≤ F) :
    (a*b-c*d)^2 ≤ 2*(E*B+A*F) := by
  have heB := mul_le_mul he hb (sq_nonneg b) hE
  have hAF := mul_le_mul hc hf (sq_nonneg (b-d)) hA
  have hs := add_sq_le (a := (a-c)*b) (b := c*(b-d))
  have hid : (a-c)*b+c*(b-d) = a*b-c*d := by ring
  rw [hid, mul_pow, mul_pow] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (add_le_add heB hAF) (by norm_num))

lemma fourth_sub_le (a b : ℝ) : |a-b|^4 ≤ 8*(|a|^4+|b|^4) := by
  have hh := pow_le_pow_left₀ (abs_nonneg (a-b)) (abs_sub a b) 4
  have hp := add_pow_le (abs_nonneg a) (abs_nonneg b) 4
  norm_num only [Nat.reduceSub, Nat.reducePow] at hp
  exact hh.trans hp

#print axioms product_difference_square_le
#print axioms fourth_sub_le
end Erdos972MeanProductErrorAlgebra
