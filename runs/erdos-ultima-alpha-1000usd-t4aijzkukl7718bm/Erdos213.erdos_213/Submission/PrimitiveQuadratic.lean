import Submission.PrimitiveQuadraticCases
import Submission.QuadraticMotion
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! A complete obstruction to quadratic-polynomial extensions of one specified
four-point family. This does not apply to higher-degree/rational-function
motions, isolated parameter values, or arbitrary integral-distance sets. -/
namespace Erdos213.PrimitiveQuadratic
open Polynomial CircleLineRigidity PrimitiveQuadraticCases
noncomputable section
set_option maxHeartbeats 1000000

lemma quadratic_square_type (a b c : ℂ)
    (hsq : IsSquare (quad a b c*(quad a b c).map (starRingEnd ℂ))) :
    b^2-4*a*c=0 ∨
      (QuadraticMotion.cross a b=0 ∧ QuadraticMotion.cross a c=0 ∧
        QuadraticMotion.cross b c=0) := by
  by_cases hd : b^2-4*a*c=0
  · exact Or.inl hd
  right
  let f := quad a b c
  have hf : f ≠ 0 := by
    intro hz
    have ha := congrArg (fun p : ℂ[X] => p.coeff 2) hz
    have hb := congrArg (fun p : ℂ[X] => p.coeff 1) hz
    simp only [f,quad_coeff_two,quad_coeff_one,coeff_zero] at ha hb
    exact hd (by simp [ha,hb])
  obtain ⟨q,hq⟩ := squarefree_dvd_partner hf (quad_separable a b c hd).squarefree hsq
  change f.map (starRingEnd ℂ) = f*q at hq
  have hg : f.map (starRingEnd ℂ) ≠ 0 := by simpa using hf
  have hq0 : q ≠ 0 := by intro hz; apply hg; simp [hq,hz]
  have hdeg := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change (f.map (starRingEnd ℂ)).natDegree=(f*q).natDegree at hdeg
  rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective,natDegree_mul hf hq0] at hdeg
  have hn : q.natDegree=0 := by omega
  rw [eq_C_of_natDegree_eq_zero hn] at hq
  have ha := congrArg (fun p : ℂ[X] => p.coeff 2) hq
  have hb := congrArg (fun p : ℂ[X] => p.coeff 1) hq
  have hc := congrArg (fun p : ℂ[X] => p.coeff 0) hq
  simp only [f,coeff_map,coeff_mul_C,quad_coeff_two,quad_coeff_one,quad_coeff_zero] at ha hb hc
  have hcross (u v : ℂ) (hu : (starRingEnd ℂ) u=u*q.coeff 0)
      (hv : (starRingEnd ℂ) v=v*q.coeff 0) : QuadraticMotion.cross u v=0 := by
    have hh : (starRingEnd ℂ) u*v=(starRingEnd ℂ) v*u := by rw [hu,hv]; ring
    have hi := congrArg Complex.im hh
    simp only [Complex.mul_im,Complex.conj_re,Complex.conj_im] at hi
    dsimp [QuadraticMotion.cross]
    linarith only [hi]
  exact ⟨hcross a b ha hb,hcross a c ha hc,hcross b c hb hc⟩

def normPolynomial (a b c : ℂ) : ℝ[X] :=
  (quad a.re b.re c.re)^2+(quad a.im b.im c.im)^2

lemma norm_type (a b c : ℂ)
    (hsq : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial a b c))) :
    lineType a.re a.im b.re b.im c.re c.im ∨
      nullType a.re a.im b.re b.im c.re c.im := by
  have hh : IsSquare (quad a b c*(quad a b c).map (starRingEnd ℂ)) := by
    rw [quad_map,quad_conjugate_product]
    obtain ⟨p,hp⟩ := polynomial_square_of_ratFunc_square _ hsq
    refine ⟨p.map (algebraMap ℝ ℂ),?_⟩
    simpa [normPolynomial,map_mul] using congrArg (Polynomial.map (algebraMap ℝ ℂ)) hp
  rcases quadratic_square_type a b c hh with hd | hc
  · right
    have hr := congrArg Complex.re hd
    have hi := congrArg Complex.im hd
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    constructor <;> dsimp [nullType]
    · nlinarith only [hr]
    · nlinarith only [hi]
  · exact Or.inl hc

/-- All real quadratic polynomial paths at symbolic square distance from the
four fixed paths stay on one of their two coordinate axes. -/
theorem quadratic_extension_axes (a b c : ℂ)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial a (b+8) c)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial a (b-8) c)))
    (h2 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a-4*Complex.I) b (c+4*Complex.I))))
    (h3 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a-16*Complex.I) b (c+Complex.I)))) :
    (a.re=0 ∧ b.re=0 ∧ c.re=0) ∨ (a.im=0 ∧ b.im=0 ∧ c.im=0) := by
  apply extension_types_axes
  · simpa using norm_type a (b+8) c h0
  · simpa using norm_type a (b-8) c h1
  · simpa using norm_type (a-4*Complex.I) b (c+4*Complex.I) h2
  · simpa using norm_type (a-16*Complex.I) b (c+Complex.I) h3

lemma collinear_of_re_zero {S : Set ℂ} (h : ∀ z ∈ S, z.re=0) : Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0 : ℂ),Complex.I,?_⟩
  intro z hz
  refine ⟨z.im,?_⟩
  rw [vadd_eq_add,add_zero,Complex.real_smul]
  apply Complex.ext <;> simp [h z hz]

lemma collinear_of_im_zero {S : Set ℂ} (h : ∀ z ∈ S, z.im=0) : Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(0 : ℂ),(1 : ℂ),?_⟩
  intro z hz
  refine ⟨z.re,?_⟩
  rw [vadd_eq_add,add_zero,Complex.real_smul]
  apply Complex.ext <;> simp [h z hz]

/-- At each real parameter, the extra path is collinear with an anchor pair.
If it is distinct from all four anchors, it cannot extend them in GP. -/
theorem quadratic_extension_collinear (a b c : ℂ)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial a (b+8) c)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (normPolynomial a (b-8) c)))
    (h2 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a-4*Complex.I) b (c+4*Complex.I))))
    (h3 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a-16*Complex.I) b (c+Complex.I)))) (t : ℝ) :
    Collinear ℝ ({(4*(t : ℂ)^2-4)*Complex.I,(16*(t : ℂ)^2-1)*Complex.I,
      a*(t : ℂ)^2+b*t+c} : Set ℂ) ∨
    Collinear ℝ ({-8*(t : ℂ),8*(t : ℂ),a*(t : ℂ)^2+b*t+c} : Set ℂ) := by
  rcases quadratic_extension_axes a b c h0 h1 h2 h3 with h | h
  · left
    apply collinear_of_re_zero
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> simp [pow_two,h.1,h.2.1,h.2.2]
  · right
    apply collinear_of_im_zero
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> simp [pow_two,h.1,h.2.1,h.2.2]

#print axioms quadratic_square_type
#print axioms quadratic_extension_axes
#print axioms quadratic_extension_collinear
end
end Erdos213.PrimitiveQuadratic
