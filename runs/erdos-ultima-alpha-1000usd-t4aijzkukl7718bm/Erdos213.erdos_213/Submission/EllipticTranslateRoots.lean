import Submission.EllipticTranslateCircle

/-! Rational root anchors for the elliptic-translation projection.
These anchors are collinear. Their distances do not imply that the
projected source points have rational mutual distances. -/
namespace Erdos213.EllipticTranslate
noncomputable section
set_option maxHeartbeats 3000000

lemma root_norm_identity {R : Type*} [CommRing R] (A B s u v e : R)
    (hu : v^2 = value A B u) (he : value A B e = 0) :
    (numerator A B s u-e*(u-s)^2)^2-4*value A B s*v^2 =
      ((u-e)*(s-e)-(3*e^2+A))^2*(u-s)^2 := by
  have hB : B = -e^3-A*e := by
    dsimp only [value] at he
    linear_combination he
  rw [hB] at hu ⊢
  dsimp only [value,numerator] at *
  linear_combination -4*(s^3+A*s-e^3-A*e)*hu

lemma root_norm (A B s u v e : ℚ)
    (hu : v^2 = value A B u) (he : value A B e = 0) (hus : u ≠ s) :
    (realPart A B s u-e)^2-value A B s*(imagCoeff s u v)^2 =
      (((u-e)*(s-e)-(3*e^2+A))/(u-s))^2 := by
  have hid := root_norm_identity A B s u v e hu he
  have hus' := sub_ne_zero.mpr hus
  dsimp only [realPart,imagCoeff]
  field_simp
  linear_combination hid

/-- Undoing the normalization makes every rational two-torsion root
an anchor at rational distance. The normalized distance itself need
not be rational. -/
theorem root_scaled_distance (A B s u v e : ℚ)
    (hs : value A B s < 0) (hu : v^2 = value A B u) (he : value A B e = 0) :
    Real.sqrt (-((value A B s : ℚ) : ℝ)) *
      dist (point A B s u v) (center A B s e) =
      ((|((u-e)*(s-e)-(3*e^2+A))/(u-s)| : ℚ) : ℝ) := by
  have hsR : ((value A B s : ℚ) : ℝ) < 0 := by exact_mod_cast hs
  have hs0 : -((value A B s : ℚ) : ℝ) ≠ 0 := by linarith
  have hs00 := ne_of_lt hsR
  have hroot := Real.sq_sqrt (show 0 ≤ -((value A B s : ℚ) : ℝ) by linarith)
  have hsq := center_dist_sq A B s u v e hs
  rw [root_norm A B s u v e hu he (on_curve_ne_source A B s u v hs hu)] at hsq
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)
    (by positivity)).mp
  rw [mul_pow,hroot,hsq]
  push_cast
  rw [sq_abs]
  field_simp [hs00]

lemma root_distance_rational (A B s u v e : ℚ)
    (hs : value A B s < 0) (hu : v^2 = value A B u) (he : value A B e = 0) :
    Real.sqrt (-((value A B s : ℚ) : ℝ)) *
      dist (point A B s u v) (center A B s e) ∈ Set.range ((↑) : ℚ → ℝ) := by
  exact ⟨_, (root_scaled_distance A B s u v e hs hu he).symm⟩

#print axioms root_norm_identity
#print axioms root_norm
#print axioms root_scaled_distance
#print axioms root_distance_rational
end
end Erdos213.EllipticTranslate
