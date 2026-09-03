import Submission.QuinticWeightedAffineNormalization
import Submission.QuinticWeightedCanonicalMoments
import Submission.QuinticWeightedResultantCertificate

/-! A complete obstruction for the normalized degree-eleven construction with
one opposite quadratic pair and two weighted affine remainders. This is not a
bound for unrestricted representations. -/
namespace Erdos322Research.QuinticWeightedAffineNoIdentity
noncomputable section
open QuinticWeightedCanonicalMoments
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem normalized_minor0 (V w : ℚ) :
    V*p0 V w*p2 V w*p4 V w-p0 V w*(p3 V w)^2-(p1 V w)^2*p4 V w+
      2*p1 V w*p2 V w*p3 V w-V*(p2 V w)^3 =
      QuinticWeightedResultantCertificate.f V w/500000000000000000000000000000 := by
  rw [QuinticWeightedResultantCertificate.f_expansion]
  dsimp [p0, p1, p2, p3, p4]
  ring

private theorem normalized_minor3 (V w : ℚ) :
    p1 V w*p3 V w*p5 V w-V*p1 V w*(p4 V w)^2-V*(p2 V w)^2*p5 V w+
      2*V*p2 V w*p3 V w*p4 V w-(p3 V w)^3 =
      -QuinticWeightedResultantCertificate.g V w/250000000000000000000000000 := by
  rw [QuinticWeightedResultantCertificate.g_expansion]
  dsimp [p1, p2, p3, p4, p5]
  ring

/-- The generic canonical chart has no rational identity. -/
theorem no_canonical_identity (v w a b c d : ℚ) (hv : v ≠ 0) :
    ¬ (∀ t : ℚ, remainder v w t+t*((a+b*t)^5+(c+d*t)^5) = 0) := by
  intro h
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := necessary_moments v w a b c d h
  have hm0 := two_affine_minor0 a b c d
  have hm3 := two_affine_minor3 a b c d
  rw [h0,h1,h2,h3,h4] at hm0
  rw [h1,h2,h3,h4,h5] at hm3
  have he0 : minor0 (v*p0 (v^2) w) (p1 (v^2) w) (v*p2 (v^2) w)
      (p3 (v^2) w) (v*p4 (v^2) w) =
      v*QuinticWeightedResultantCertificate.f (v^2) w/500000000000000000000000000000 := by
    calc
      _ = v*((v^2)*p0 (v^2) w*p2 (v^2) w*p4 (v^2) w-
          p0 (v^2) w*(p3 (v^2) w)^2-(p1 (v^2) w)^2*p4 (v^2) w+
          2*p1 (v^2) w*p2 (v^2) w*p3 (v^2) w-(v^2)*(p2 (v^2) w)^3) := by
            unfold minor0
            ring
      _ = _ := by rw [normalized_minor0]; ring
  have he3 : minor3 (p1 (v^2) w) (v*p2 (v^2) w) (p3 (v^2) w)
      (v*p4 (v^2) w) (p5 (v^2) w) =
      -QuinticWeightedResultantCertificate.g (v^2) w/250000000000000000000000000 := by
    calc
      _ = p1 (v^2) w*p3 (v^2) w*p5 (v^2) w-
          (v^2)*p1 (v^2) w*(p4 (v^2) w)^2-(v^2)*(p2 (v^2) w)^2*p5 (v^2) w+
          2*(v^2)*p2 (v^2) w*p3 (v^2) w*p4 (v^2) w-(p3 (v^2) w)^3 := by
            unfold minor3
            ring
      _ = _ := normalized_minor3 _ _
  rw [he0] at hm0
  rw [he3] at hm3
  have hf : QuinticWeightedResultantCertificate.f (v^2) w = 0 := by
    have he : v*QuinticWeightedResultantCertificate.f (v^2) w = 0 := by
      linear_combination 500000000000000000000000000000*hm0
    exact (mul_eq_zero.mp he).resolve_left hv
  have hg : QuinticWeightedResultantCertificate.g (v^2) w = 0 := by
    linear_combination -250000000000000000000000000*hm3
  exact QuinticWeightedResultantCertificate.no_common_rational_root _ _ ⟨hf,hg⟩

/-- Both coefficient charts of this normalized polynomial family are
impossible. No sign or nondegeneracy assumptions are imposed on its remaining
parameters. This does not classify arbitrary quintic polynomial identities. -/
theorem no_normalized_identity (S H c₀ D z q a b c d : ℚ) :
    ¬ (∀ t : ℚ,
      t*((((S+H*t)/2)+(t^2+c₀*t+D))^5+
        (((S+H*t)/2)-(t^2+c₀*t+D))^5+(a+b*t)^5+(c+d*t)^5)+
      (t^2+z*t+q)^5 = q^5) := by
  intro hid
  obtain ⟨v,hv,w,h⟩ :=
    QuinticWeightedAffineNormalization.canonical_reduction S H c₀ D z q a b c d hid
  exact no_canonical_identity v w a b c d hv h

end
end Erdos322Research.QuinticWeightedAffineNoIdentity
