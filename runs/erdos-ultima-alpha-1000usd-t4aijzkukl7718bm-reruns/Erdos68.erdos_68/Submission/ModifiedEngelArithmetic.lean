import Submission.NormalizedEngel

/-!
# Arithmetic coordinates for a modified Engel step

This is auxiliary work, not a proof or disproof of Erdős 68. The coordinate
u = 1 + 1/r gives an integral fractional-linear matrix, but its determinant
is (B-1)^2 rather than one. We also characterize all cancellation factors
in a rational remainder update.
-/

namespace ModifiedEngelArithmetic

lemma inverse_coordinate_update (B u : ℝ) (hu : 1 < u) (hB : u < B) :
    1 + 1 / (1 / (u - 1) - 1 / (B - 1)) =
      ((B - 2) * u + 1) / (B - u) := by
  have hu0 : u - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  have hB0 : B - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (hu.trans hB))
  have hBu : B - u ≠ 0 := ne_of_gt (sub_pos.mpr hB)
  have hdiff : 1 / (u - 1) - 1 / (B - 1) =
      (B-u) / ((u-1)*(B-1)) := by
    field_simp [hu0, hB0]
    ring
  rw [hdiff, one_div_div]
  field_simp [hBu]
  ring

/-- The coordinate matrix has entries B-2, 1, -1, B. -/
lemma coordinate_determinant (B : ℤ) :
    (B - 2) * B - 1 * (-1) = (B - 1)^2 := by ring

lemma coordinate_determinant_large (B : ℤ) (hB : 3 ≤ B) :
    4 ≤ (B - 2) * B - 1 * (-1) := by nlinarith

/-- Under a coprime rational representation a/b, cancellation in
(da-b)/(db) is exactly cancellation with d^2. -/
theorem common_divisor_iff (a b d c : ℤ) (hab : IsCoprime a b) :
    (c ∣ d*a - b ∧ c ∣ d*b) ↔ (c ∣ d*a - b ∧ c ∣ d^2) := by
  obtain ⟨u, v, huv⟩ := hab
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have hh : c ∣ (u*d)*(d*a-b) + (u+v*d)*(d*b) :=
      dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)
    have he : (u*d)*(d*a-b) + (u+v*d)*(d*b) = d^2 := by
      calc
        _ = d^2 * (u*a+v*b) := by ring
        _ = d^2 := by rw [huv, mul_one]
    rwa [he] at hh
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have hh : c ∣ a*d^2 - d*(d*a-b) :=
      dvd_sub (dvd_mul_of_dvd_right hy _) (dvd_mul_of_dvd_right hx _)
    convert hh using 1; ring

/-- A coprime new denominator cannot cancel any part of the unreduced
updated denominator. -/
theorem new_coprime_denominator (a b d : ℤ)
    (hab : IsCoprime a b) (hbd : IsCoprime b d) :
    IsCoprime (d*a-b) (d*b) := by
  obtain ⟨u, v, huv⟩ := hab
  obtain ⟨s, t, hst⟩ := hbd
  have hxad : IsCoprime (d*a-b) a := by
    refine ⟨-v, u+v*d, ?_⟩
    nlinarith [huv]
  have hxdd : IsCoprime (d*a-b) d := by
    refine ⟨-s, t+s*a, ?_⟩
    nlinarith [hst]
  have hx_bd : IsCoprime (d*a-b) b := by
    obtain ⟨s', t', hst'⟩ := hxdd.mul_right hxad
    refine ⟨s'+t', t', ?_⟩
    convert hst' using 1; ring
  exact hxdd.mul_right hx_bd

#print axioms inverse_coordinate_update
#print axioms common_divisor_iff
#print axioms new_coprime_denominator

end ModifiedEngelArithmetic
