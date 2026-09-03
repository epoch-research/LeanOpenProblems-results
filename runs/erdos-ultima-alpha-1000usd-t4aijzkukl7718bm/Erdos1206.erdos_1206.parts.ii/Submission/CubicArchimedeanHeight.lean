import Submission.CubicBaseLocus

/-!
A uniform archimedean height estimate for the cubic parametrization.
This concerns the raw coordinates before division by their common factor.
It is not a density estimate for the primitive reduced roots.
-/

namespace Erdos1206.CubicBaseLocus

lemma coordinate_square_sum_identity (a b t : ℝ) :
    A a b t ^ 2 + B a b t ^ 2 + C a b t ^ 2 + D a b t ^ 2 =
      4*t^6 + 2*((a-2*b)^2+(a+b)^2)*t^4 +
      12*(a^2+(a-b)^2)*t^4 + 18*(a^4+(a-b)^4)*t^2 +
      24*(Q a b)^2*t^2 + 18*(Q a b)^2*(a^2+(a-b)^2) := by
  dsimp [A,B,C,D,Q]
  ring

/-- A cubic lower bound for the Euclidean norm of the four raw coordinates. -/
theorem coordinate_square_sum_lower (a b t : ℝ) :
    (a^2+b^2+t^2)^3 ≤ A a b t ^ 2 + B a b t ^ 2 + C a b t ^ 2 + D a b t ^ 2 := by
  let U : ℝ := a^2+b^2
  let R : ℝ := a^2+(a-b)^2
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hUQ : U ≤ 2*Q a b := by
    dsimp [U,Q]
    nlinarith [sq_nonneg (a-b)]
  have hUR : U ≤ 3*R := by
    dsimp [U,R]
    nlinarith [sq_nonneg (2*a-b),sq_nonneg (a-b)]
  have hU2 : U^2 ≤ 4*(Q a b)^2 := by
    have hh := pow_le_pow_left₀ hU0 hUQ 2
    nlinarith only [hh]
  have hU3 : U^3 ≤ 12*(Q a b)^2*R := by
    have hh := mul_le_mul hU2 hUR hU0 (show 0 ≤ 4*(Q a b)^2 by positivity)
    nlinarith only [hh]
  have hd1 : 0 ≤ 12*(Q a b)^2*R-U^3 := sub_nonneg.mpr hU3
  have hd2 : 0 ≤ 4*(Q a b)^2-U^2 := sub_nonneg.mpr hU2
  have hd3 : 0 ≤ 3*R-U := sub_nonneg.mpr hUR
  have hid : A a b t ^ 2 + B a b t ^ 2 + C a b t ^ 2 + D a b t ^ 2 -
      (a^2+b^2+t^2)^3 =
      (12*(Q a b)^2*R-U^3) + 3*(4*(Q a b)^2-U^2)*t^2 +
      3*(3*R-U)*t^4 +
      (3*t^6 + 2*((a-2*b)^2+(a+b)^2)*t^4 + 3*R*t^4 +
        18*(a^4+(a-b)^4)*t^2 + 12*(Q a b)^2*t^2 + 6*(Q a b)^2*R) := by
    rw [coordinate_square_sum_identity]
    dsimp [U,R]
    ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

/-- If all four raw coordinates have absolute value at most H, each parameter
has cube of its absolute value at most 2H. -/
theorem parameter_height_bound (a b t H : ℝ) (hH : 0 ≤ H)
    (ha : |A a b t| ≤ H) (hb : |B a b t| ≤ H)
    (hc : |C a b t| ≤ H) (hd : |D a b t| ≤ H) :
    |a|^3 ≤ 2*H ∧ |b|^3 ≤ 2*H ∧ |t|^3 ≤ 2*H := by
  have hsq (x : ℝ) (hx : |x| ≤ H) : x^2 ≤ H^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hH).mpr hx
  have hs : A a b t ^ 2 + B a b t ^ 2 + C a b t ^ 2 + D a b t ^ 2 ≤ 4*H^2 := by
    linarith [hsq _ ha,hsq _ hb,hsq _ hc,hsq _ hd]
  have hnorm := coordinate_square_sum_lower a b t
  have hparam (z : ℝ) (hz : z^2 ≤ a^2+b^2+t^2) : |z|^3 ≤ 2*H := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ |z|^3) (by positivity : 0 ≤ 2*H)).mp
    calc
      (|z|^3)^2 = (z^2)^3 := by rw [← pow_mul, mul_comm 3 2, pow_mul, sq_abs]
      _ ≤ (a^2+b^2+t^2)^3 := pow_le_pow_left₀ (sq_nonneg z) hz 3
      _ ≤ 4*H^2 := hnorm.trans hs
      _ = (2*H)^2 := by ring
  exact ⟨hparam a (by nlinarith [sq_nonneg b,sq_nonneg t]),
    hparam b (by nlinarith [sq_nonneg a,sq_nonneg t]),
    hparam t (by nlinarith [sq_nonneg a,sq_nonneg b])⟩

/-- The same bound after writing each raw coordinate as a common positive
factor times a reduced coordinate. The factor must not be discarded. -/
theorem parameter_height_bound_with_cancellation (a b t g H : ℝ)
    (hg : 0 ≤ g) (hH : 0 ≤ H)
    (ha : |A a b t| ≤ g*H) (hb : |B a b t| ≤ g*H)
    (hc : |C a b t| ≤ g*H) (hd : |D a b t| ≤ g*H) :
    |a|^3 ≤ 2*g*H ∧ |b|^3 ≤ 2*g*H ∧ |t|^3 ≤ 2*g*H := by
  simpa only [mul_assoc] using parameter_height_bound a b t (g*H) (mul_nonneg hg hH) ha hb hc hd

#print axioms coordinate_square_sum_lower
#print axioms parameter_height_bound
#print axioms parameter_height_bound_with_cancellation

end Erdos1206.CubicBaseLocus
