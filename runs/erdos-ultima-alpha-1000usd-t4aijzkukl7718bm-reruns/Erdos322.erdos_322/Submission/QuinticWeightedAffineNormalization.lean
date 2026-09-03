import Submission.QuinticWeightedAffineExceptional
import Submission.QuinticWeightedCanonicalMoments

/-! An exact normalization for a restricted quintic construction. -/
namespace Erdos322Research.QuinticWeightedAffineNormalization
noncomputable section
open QuinticWeightedCanonicalMoments
set_option Elab.async false
set_option maxHeartbeats 0

private theorem regroup (t p q r s y n : ℚ)
    (h : t*(p+q+r+s)+y=n) : t*(p+q)+y-n+t*(r+s)=0 := by
  linear_combination h

/-- Any identity in this normalized leading-coefficient family would give
a point in its canonical nonzero-determinant chart. -/
theorem canonical_reduction (S H c₀ D z q a b c d : ℚ)
    (hid : ∀ t : ℚ,
      t*((((S+H*t)/2)+(t^2+c₀*t+D))^5+
        (((S+H*t)/2)-(t^2+c₀*t+D))^5+(a+b*t)^5+(c+d*t)^5)+
      (t^2+z*t+q)^5 = q^5) :
    ∃ v : ℚ, v ≠ 0 ∧ ∃ w : ℚ,
      ∀ t : ℚ, remainder v w t+t*((a+b*t)^5+(c+d*t)^5) = 0 := by
  by_cases hz : c₀ = z
  · exact (QuinticWeightedAffineExceptional.no_equal_middle_identity S H c₀ D z q a b c d hz hid).elim
  · obtain ⟨he10,he9,he8,he7⟩ :=
      QuinticWeightedAffineExceptional.identity_high_constraints S H c₀ D z q a b c d hid
    have hH : H = -1/5 := by linarith
    have hS : S = 4*c₀/5-z := by rw [hH] at he9; linarith
    let v : ℚ := z-c₀
    let w : ℚ := z/v
    have hv : v ≠ 0 := sub_ne_zero.mpr (fun h => hz h.symm)
    have hz' : z = v*w := by dsimp [w]; field_simp
    have hc' : c₀ = v*(w-1) := by
      have he : c₀ = z-v := by dsimp [v]; ring
      rw [he, hz']
      ring
    have hS' : S = -v*(w+4)/5 := by rw [hS, hc', hz']; ring
    rw [hH,hS',hc',hz'] at he8 he7
    have hD : D = constX v w := by
      have he : v*(D-constX v w) = 0 := by
        dsimp [constX]
        linear_combination (4*v*w*he8-he7)/4
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hv)
    have hq : q = constY v w := by
      rw [hD] at he8
      dsimp [constX] at he8
      dsimp [constY]
      linear_combination he8/5
    refine ⟨v, hv, w, ?_⟩
    intro t
    have ht := hid t
    rw [hH,hS',hc',hz',hD,hq] at ht
    have hP : -v*(w+4)/5+(-1/5)*t = -v*(w+4)/5-t/5 := by ring
    rw [hP] at ht
    dsimp [remainder]
    exact regroup t _ _ _ _ _ _ ht


end
end Erdos322Research.QuinticWeightedAffineNormalization
