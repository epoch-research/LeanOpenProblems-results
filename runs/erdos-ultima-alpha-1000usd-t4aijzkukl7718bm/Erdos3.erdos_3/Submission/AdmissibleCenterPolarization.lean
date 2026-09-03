import Submission.RobustBohrLinearization

/-! Polarization transport between arbitrary admissible centers. -/
namespace Erdos3AdmissibleCenterPolarization
open Erdos3LocalQuadraticPolarization Erdos3LocalQuadraticProgressions
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity
open scoped ComplexConjugate
variable {G : Type*} [AddCommGroup G]

/-- Only the eight vertices must lie in the domain; the long displacement
between the centers need not belong to it. -/
theorem localPolar_centers {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (b c h x : G)
    (hb : b ∈ R) (hbh : b+h ∈ R) (hbx : b+x ∈ R) (hbxh : (b+x)+h ∈ R)
    (hc : c ∈ R) (hch : c+h ∈ R) (hcx : c+x ∈ R) (hcxh : (c+x)+h ∈ R) :
    localPolar (fun y ↦ q (c+y)) h x =
      localPolar (fun y ↦ q (b+y)) h x := by
  have hcancel : b+(c-b) = c := by abel
  have he := hquad b h x (c-b) hb hbh hbx hbxh
    (by simpa only [hcancel] using hc)
    (by simpa only [hcancel] using hch)
    (by simpa only [hcancel] using hcx)
    (by simpa only [hcancel] using hcxh)
  change derivative (derivative q h) x (b+(c-b))*
    conj (derivative (derivative q h) x b) = 1 at he
  have ht := unit_conj_cancel
    (derivative_norm_one (derivative q h) (derivative_norm_one q hq h) x b) he
  simp only [one_mul, hcancel] at ht
  simpa only [localPolar, derivative, zero_add, add_zero, add_assoc] using ht

#print axioms localPolar_centers
end Erdos3AdmissibleCenterPolarization
