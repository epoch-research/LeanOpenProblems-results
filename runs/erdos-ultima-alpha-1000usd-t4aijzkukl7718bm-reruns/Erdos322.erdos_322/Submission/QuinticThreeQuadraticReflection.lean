import FormalConjecturesUtil

/-! A coefficient obstruction in a restricted reflection-symmetric quintic
construction. This does not bound unrestricted representation counts. -/
namespace Erdos322Research.QuinticThreeQuadraticReflection

open Polynomial
noncomputable section
set_option maxHeartbeats 0

/-- The normalized model when the constant offset in the paired coordinates
is zero. The two reflected quadratic remainders have leading-weight ratio `-b`. -/
def model (a w z b : ℝ) : ℝ[X] :=
  C (2*b-1)*(X^5+C (1/2)*X^4+C (1/80)*X^3)+(X+C a)^5-
    C (2*b)*((X-C w)^5+C (10*z)*X*(X-C w)^3+C (5*z^2)*X^2*(X-C w))

private lemma coefficient_two (a w z b : ℝ) :
    (model a w z b).coeff 2 =
      10*a^3+20*b*w^3-60*b*z*w^2+10*b*z^2*w := by
  dsimp [model]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C,
    coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num
  ring

private lemma coefficient_three (a w z b : ℝ) :
    (model a w z b).coeff 3 =
      (2*b-1)/80+10*a^2-20*b*w^2+60*b*z*w-10*b*z^2 := by
  dsimp [model]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_sub, coeff_neg, coeff_mul_C,
    coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num
  ring

/-- There is no constant identity at any nonnegative parameter where the
unpaired remainder and the mean of the reflected pair have the required
positive signs. No assumption that `a` itself is positive is made. -/
theorem no_positive_constant_identity (a w z b u N : ℝ)
    (hb : 1/2 < b) (hu : 0 ≤ u) (ha : 0 < u+a) (hw : u < w) :
    model a w z b ≠ C N := by
  intro h
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) h
  have h3 := congrArg (fun p : ℝ[X] => p.coeff 3) h
  dsimp only at h2 h3
  rw [coefficient_two] at h2
  rw [coefficient_three] at h3
  norm_num at h2 h3
  have hw0 : 0 < w := lt_of_le_of_lt hu hw
  have hwa : 0 < w+a := by linarith
  have hb0 : 0 < 2*b-1 := by linarith
  have hp : 0 < w*(2*b-1)/80 := by positivity
  have hn : 0 ≤ 10*a^2*(w+a) := by positivity
  have he : w*(2*b-1)/80+10*a^2*(w+a)=0 := by
    linear_combination w*h3+h2
  linarith

end
end Erdos322Research.QuinticThreeQuadraticReflection
