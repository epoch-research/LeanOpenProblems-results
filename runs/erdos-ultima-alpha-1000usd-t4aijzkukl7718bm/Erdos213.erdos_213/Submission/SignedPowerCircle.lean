import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A geometric obstruction to the consecutive signed-power template.
No assertion about arbitrary integral-distance configurations is made. -/
namespace Erdos213.SignedPowerCircle

private lemma dist_sq (z w : ℂ) :
    dist z w^2=(z.re-w.re)^2+(z.im-w.im)^2 := by
  rw [dist_eq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

noncomputable def center (z : ℂ) : ℂ :=
  ⟨(1-(z.re^2+z.im^2))/2, z.re*(z.re^2+z.im^2-1)/(2*z.im)⟩

/-- For every nonreal z, the four points 1,z,-z,z² are concyclic. -/
theorem cospherical_signed_powers {z : ℂ} (hz : z.im≠0) :
    EuclideanGeometry.Cospherical ({1,z,-z,z^2} : Set ℂ) := by
  refine ⟨center z, dist z (center z), ?_⟩
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl|rfl|rfl|rfl
  all_goals try rfl
  all_goals
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [dist_sq,dist_sq]
    simp only [center, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
      pow_two, Complex.mul_re, Complex.mul_im]
    field_simp
    ring

#print axioms cospherical_signed_powers

end Erdos213.SignedPowerCircle
