import Submission.EllipticTorsionCap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! Reflection geometry for the restricted elliptic torsion model.
No classification of rational torsion, or reduction of arbitrary rational-distance
sets to this model, is assumed or asserted. -/
namespace Erdos213.EllipticTorsionCap
open EuclideanGeometry
noncomputable section

private lemma complex_dist_sq (z w : ℂ) :
    dist z w ^ 2 = (z.re-w.re)^2+(z.im-w.im)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp [pow_two]

lemma conjugate_pairs_cospherical (z w : ℂ) (h : z.re ≠ w.re) :
    Cospherical ({z,starRingEnd ℂ z,w,starRingEnd ℂ w} : Set ℂ) := by
  let o : ℝ := (z.re^2+z.im^2-w.re^2-w.im^2)/(2*(z.re-w.re))
  have hd : 2*(z.re-w.re) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr h)
  have ho : 2*(z.re-w.re)*o = z.re^2+z.im^2-w.re^2-w.im^2 := by
    dsimp [o]
    field_simp [sub_ne_zero.mpr h]
  refine ⟨(o : ℂ),dist z (o : ℂ),?_⟩
  rintro p (rfl | rfl | rfl | rfl)
  · rfl
  all_goals
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [complex_dist_sq,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im]
    nlinarith

/-- Conditional bridge from the finite certificate to the reflection model.
The zero-sum incidence condition and separation of real coordinates are explicit
hypotheses, not a claimed classification of all plane configurations. -/
lemma eight_reflection_not_gp (S : Finset G) (hc : S.card = 8)
    (h0 : (0 : G) ∉ S) (ht : NoThreeSum S) (z : G → ℂ)
    (hneg : ∀ a ∈ S, z (-a) = starRingEnd ℂ (z a))
    (hx : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ≠ -b → (z a).re ≠ (z b).re)
    (hgp : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬Cospherical ({z a,z b,z c,z d} : Set ℂ)) : False := by
  obtain ⟨a,ha,b,hb,hna,hnb,han,hbn,hab,hanb⟩ := eight_has_opposite_pairs S hc h0 ht
  have hnab : -a ≠ b := by
    intro he
    apply hanb
    simpa using congrArg Neg.neg he
  have hn : -a ≠ -b := by simpa using hab
  have he := conjugate_pairs_cospherical (z a) (z b) (hx a ha b hb hab hanb)
  rw [← hneg a ha,← hneg b hb] at he
  exact hgp a ha (-a) hna b hb (-b) hnb han hab hanb hnab hn hbn he

private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- The circle determinant for two opposite pairs in a general affine metric.
It need not vanish for an oblique shear. -/
lemma oblique_pair_determinant {R : Type*} [CommRing R] (a b c d A B C : R) :
    det3 0 (-2*b) (-4*B*a*b)
      (c-a) (d-b) (A*c^2+2*B*c*d+C*d^2-(A*a^2+2*B*a*b+C*b^2))
      (c-a) (-d-b) (A*c^2-2*B*c*d+C*d^2-(A*a^2+2*B*a*b+C*b^2)) =
      -8*B*b*d*(a-c)^2 := by
  dsimp [det3]
  ring

#print axioms conjugate_pairs_cospherical
#print axioms eight_reflection_not_gp
#print axioms oblique_pair_determinant
end
end Erdos213.EllipticTorsionCap
