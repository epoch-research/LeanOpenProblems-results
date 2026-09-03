import Submission.ReciprocalStar

/-! A Joukowski reformulation of the signed-power norm conditions.
This gives implications between conditional constructions, not a witness. -/
namespace Erdos213.SignedPowerSpokes
open Erdos213.ReciprocalStar

private lemma rationalNorm_sq {z : ℂ} (h : RationalNorm z) : RationalNorm (z^2) := by
  simpa only [pow_two] using h.mul h

noncomputable def joukowski (z : ℂ) : ℂ := z+z⁻¹

lemma shift_zero (z : ℂ) (hz : z≠0) : joukowski z=(z^2+1)/z := by
  unfold joukowski
  field_simp

lemma shift_minus_one (z : ℂ) (hz : z≠0) : joukowski z-1=(z^2-z+1)/z := by
  unfold joukowski
  field_simp
  ring

lemma shift_plus_one (z : ℂ) (hz : z≠0) : joukowski z+1=(z^2+z+1)/z := by
  unfold joukowski
  field_simp
  ring

lemma shift_minus_two (z : ℂ) (hz : z≠0) : joukowski z-2=(z-1)^2/z := by
  unfold joukowski
  field_simp
  ring

lemma shift_plus_two (z : ℂ) (hz : z≠0) : joukowski z+2=(z+1)^2/z := by
  unfold joukowski
  field_simp
  ring

lemma fourth_power (z : ℂ) (hz : z≠0) : (joukowski z)^2-2=(z^4+1)/z^2 := by
  unfold joukowski
  field_simp
  ring

/-- The six signed-power norms yield five equally spaced rational spokes. -/
theorem five_rational_spokes {z : ℂ} (hz : z≠0)
    (hN : RationalNorm z) (hm : RationalNorm (z-1)) (hp : RationalNorm (z+1))
    (h4 : RationalNorm (z^2+1))
    (h6 : RationalNorm (z^2-z+1)) (h3 : RationalNorm (z^2+z+1)) :
    RationalNorm (joukowski z) ∧
      RationalNorm (joukowski z-1) ∧ RationalNorm (joukowski z+1) ∧
      RationalNorm (joukowski z-2) ∧ RationalNorm (joukowski z+2) := by
  rw [shift_minus_one z hz, shift_plus_one z hz,
    shift_minus_two z hz, shift_plus_two z hz, shift_zero z hz]
  exact ⟨h4.div hN,h6.div hN,h3.div hN,
    (rationalNorm_sq hm).div hN,(rationalNorm_sq hp).div hN⟩

lemma extra_norm {z : ℂ} (hz : z≠0) (hN : RationalNorm z)
    (h8 : RationalNorm (z^4+1)) : RationalNorm ((joukowski z)^2-2) := by
  rw [fourth_power z hz]
  exact h8.div (rationalNorm_sq hN)

#print axioms five_rational_spokes
#print axioms extra_norm

end Erdos213.SignedPowerSpokes
