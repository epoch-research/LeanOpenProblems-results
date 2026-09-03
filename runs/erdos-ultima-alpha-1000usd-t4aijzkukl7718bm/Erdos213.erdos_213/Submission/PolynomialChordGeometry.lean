import Submission.PolynomialChordRigidity
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Geometric form of the uniform polynomial-path rigidity theorem. -/
namespace Erdos213.PolynomialChordGeometry
open Polynomial PolynomialChordRigidity
noncomputable section
set_option maxHeartbeats 1000000

lemma complex_dependent {z w : ℂ} (hz : z ≠ 0)
    (h : z.re*w.im-z.im*w.re=0) : ∃ r : ℝ, w=r • z := by
  by_cases hx : z.re=0
  · have hy : z.im ≠ 0 := by
      intro hh
      apply hz
      exact Complex.ext hx hh
    have hw : w.re=0 := by
      rw [hx,zero_mul,zero_sub,neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hy
    refine ⟨w.im/z.im,?_⟩
    apply Complex.ext
    · simp [hx,hw]
    · simp [hy]
  · refine ⟨w.re/z.re,?_⟩
    apply Complex.ext
    · simp [hx]
    · simp only [Complex.smul_im,smul_eq_mul]
      field_simp
      nlinarith only [h]

lemma range_collinear_of_cross {ι : Type*} [Nonempty ι] (p : ι → ℂ)
    (h : ∀ s t u, ((p t).re-(p s).re)*((p u).im-(p s).im)-
      ((p t).im-(p s).im)*((p u).re-(p s).re)=0) :
    Collinear ℝ (Set.range p) := by
  classical
  let a : ι := Classical.arbitrary ι
  by_cases hc : ∀ b, p b=p a
  · rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨p a,(0 : ℂ),?_⟩
    rintro _ ⟨b,rfl⟩
    exact ⟨0,by simpa using hc b⟩
  · push_neg at hc
    obtain ⟨b,hb⟩ := hc
    rw [collinear_iff_of_mem (Set.mem_range_self a)]
    refine ⟨p b-p a,?_⟩
    rintro _ ⟨t,rfl⟩
    obtain ⟨r,hr⟩ := complex_dependent (sub_ne_zero.mpr hb)
      (show (p b-p a).re*(p t-p a).im-(p b-p a).im*(p t-p a).re=0 by
        simpa only [Complex.sub_re,Complex.sub_im] using h a b t)
    exact ⟨r,by simpa using (sub_eq_iff_eq_add.mp hr)⟩

def point (D : ℚ) (x y : ℚ[X]) (t : ℚ) : ℂ :=
  ((x.eval t : ℚ) : ℂ)+((y.eval t : ℚ) : ℂ)*(Real.sqrt (D : ℝ) : ℂ)*Complex.I

lemma point_dist_sq (D : ℚ) (hD : 0 ≤ D) (x y : ℚ[X]) (s t : ℚ) :
    dist (point D x y s) (point D x y t)^2 =
      (((x.eval s-x.eval t)^2+D*(y.eval s-y.eval t)^2 : ℚ) : ℝ) := by
  have hDr : (0 : ℝ) ≤ D := by exact_mod_cast hD
  rw [dist_eq_norm,← Complex.normSq_eq_norm_sq]
  simp only [point,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ratCast_re,Complex.ratCast_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
  push_cast
  linear_combination (((y.eval s : ℚ) : ℝ)-y.eval t)^2 * Real.sq_sqrt hDr

/-- The complete rational-parameter image is collinear, not merely the
integer parameters at which the distance hypotheses are imposed. -/
theorem uniform_rational_distances_collinear (D : ℚ) (hD : 0 < D) (x y : ℚ[X])
    (h : ∃ N : ℤ, ∀ m n : ℤ, N ≤ m → N ≤ n →
      dist (point D x y (m : ℚ)) (point D x y (n : ℚ))
        ∈ Set.range ((↑) : ℚ → ℝ)) :
    Collinear ℝ (Set.range (point D x y)) := by
  obtain ⟨N,hN⟩ := h
  have hint : ∃ N : ℤ, ∀ m n : ℤ, N ≤ m → N ≤ n →
      IsSquare ((x.eval (m : ℚ)-x.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)-y.eval (n : ℚ))^2) := by
    refine ⟨N,?_⟩
    intro m n hm hn
    obtain ⟨r,hr⟩ := hN m n hm hn
    have he := point_dist_sq D hD.le x y (m : ℚ) (n : ℚ)
    rw [← hr] at he
    refine ⟨r,?_⟩
    apply Rat.cast_injective (α := ℝ)
    push_cast
    push_cast at he
    nlinarith only [he]
  apply range_collinear_of_cross
  intro s t u
  have he := all_chords_collinear D hD x y hint s t u
  have hr : (((x.eval t : ℚ) : ℝ)-x.eval s)*(((y.eval u : ℚ) : ℝ)-y.eval s)-
      (((y.eval t : ℚ) : ℝ)-y.eval s)*(((x.eval u : ℚ) : ℝ)-x.eval s)=0 := by exact_mod_cast he
  simp only [point,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ratCast_re,Complex.ratCast_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
  linear_combination Real.sqrt (D : ℝ)*hr

#print axioms range_collinear_of_cross
#print axioms point_dist_sq
#print axioms uniform_rational_distances_collinear
end
end Erdos213.PolynomialChordGeometry
