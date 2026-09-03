import Submission.RationalChordPencil
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Geometric consequence of the symbolic rational-function pencil argument.
The square hypotheses here are polynomial identities, not isolated square
values. The arithmetic bridge for sampled rational distances is provided in
`Submission.RationalChordUniform`. -/
namespace Erdos213.RationalChordCircle
open Polynomial EuclideanGeometry RationalChordPencil
noncomputable section
set_option maxHeartbeats 2000000

lemma phase_line {z k : ℂ} (hk : k≠0)
    (h : k*(starRingEnd ℂ z)*(z-1)=k*z*(starRingEnd ℂ z-1)) : z.im=0 := by
  have he : k*(z-starRingEnd ℂ z)=0 := by linear_combination h
  have he' := (mul_eq_zero.mp he).resolve_left hk
  have hz : starRingEnd ℂ z=z := (sub_eq_zero.mp he').symm
  exact Complex.conj_eq_iff_im.mp hz

lemma phase_circle {z k l : ℂ} (hkl : l-k≠0)
    (h : l*(starRingEnd ℂ z)*(z-1)=k*z*(starRingEnd ℂ z-1)) :
    Complex.normSq z = z.re + (-Complex.I*(k+l)/(l-k)).re*z.im := by
  have he : (l-k)*((Complex.normSq z : ℂ)-(z.re : ℂ)) =
      -Complex.I*(k+l)*(z.im : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    have hz : (z.re : ℂ)=(z+starRingEnd ℂ z)/2 := by
      apply Complex.ext <;> simp
    have hi : (z.im : ℂ)*Complex.I=(z-starRingEnd ℂ z)/2 := by
      apply Complex.ext <;> simp
    calc
      _ = (l-k)*((starRingEnd ℂ z)*z-(z+starRingEnd ℂ z)/2) := by rw [hz]
      _ = -(k+l)*((z-starRingEnd ℂ z)/2) := by linear_combination h
      _ = _ := by rw [← hi]; ring
  have hh : ((Complex.normSq z : ℂ)-(z.re : ℂ)) =
      (-Complex.I*(k+l)/(l-k))*(z.im : ℂ) := by
    apply (mul_left_cancel₀ hkl)
    field_simp
    linear_combination he
  have hr := congrArg Complex.re hh
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hr
  linarith

lemma circle_equation_dist {z : ℂ} (q : ℝ)
    (h : Complex.normSq z=z.re+q*z.im) :
    dist z ((1/2 : ℂ)+(q/2 : ℂ)*Complex.I) =
      ‖(1/2 : ℂ)+(q/2 : ℂ)*Complex.I‖ := by
  rw [dist_eq_norm]
  have he : Complex.normSq (z-((1/2 : ℂ)+(q/2 : ℂ)*Complex.I)) =
      Complex.normSq ((1/2 : ℂ)+(q/2 : ℂ)*Complex.I) := by
    simp [Complex.normSq_apply] at h ⊢
    nlinarith
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma phase_of_two_conjugates (A B u v k l : ℂ) (hB : B≠0) (huv : u≠v)
    (hu : starRingEnd ℂ (A-u*B)=k*(A-u*B))
    (hv : starRingEnd ℂ (A-v*B)=l*(A-v*B)) :
    let z := (A/B-u)/(v-u)
    l*(starRingEnd ℂ z)*(z-1)=k*z*(starRingEnd ℂ z-1) := by
  let E := A-u*B
  let F := A-v*B
  let D := B*(v-u)
  have hvu : v-u≠0 := sub_ne_zero.mpr (Ne.symm huv)
  have hD : D≠0 := mul_ne_zero hB (sub_ne_zero.mpr (Ne.symm huv))
  have hbarD : starRingEnd ℂ D≠0 := (_root_.map_ne_zero (starRingEnd ℂ)).mpr hD
  have hz : (A/B-u)/(v-u)=E/D := by dsimp [E,D]; field_simp
  have hzm : E/D-1=F/D := by dsimp [E,F,D]; field_simp [hvu]; ring
  have hcross : l*(starRingEnd ℂ E)*F=k*E*(starRingEnd ℂ F) := by
    rw [show starRingEnd ℂ E=k*E from hu,show starRingEnd ℂ F=l*F from hv]
    ring
  dsimp only
  rw [hz,hzm,show starRingEnd ℂ (E/D)-1=starRingEnd ℂ (F/D) by
    rw [← hzm,map_sub,map_one]]
  simp only [map_div₀]
  field_simp
  linear_combination hcross

/-- A fixed phase relation after similarity normalization describes a line or
a circle, uniformly for the whole set. -/
lemma line_or_circle_of_phase (S : Set ℂ) (u v k l : ℂ) (huv : u≠v) (hk : k≠0)
    (h : ∀ z∈S,
      let w := (z-u)/(v-u)
      l*(starRingEnd ℂ w)*(w-1)=k*w*(starRingEnd ℂ w-1)) :
    Collinear ℝ S ∨ Cospherical S := by
  have hd : v-u≠0 := sub_ne_zero.mpr (Ne.symm huv)
  by_cases hkl : l=k
  · left
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨u,v-u,?_⟩
    intro z hz
    have hi : ((z-u)/(v-u)).im=0 := phase_line hk (by simpa only [hkl] using h z hz)
    have hw : (((z-u)/(v-u)).re : ℂ)=(z-u)/(v-u) := by
      apply Complex.ext <;> simp [hi]
    refine ⟨((z-u)/(v-u)).re,?_⟩
    rw [vadd_eq_add,Complex.real_smul,hw,div_mul_cancel₀ _ hd]
    ring
  · right
    let q : ℝ := (-Complex.I*(k+l)/(l-k)).re
    let c : ℂ := (1/2 : ℂ)+(q/2 : ℂ)*Complex.I
    refine ⟨u+(v-u)*c,‖v-u‖*‖c‖,?_⟩
    intro z hz
    have hw := circle_equation_dist q (phase_circle (sub_ne_zero.mpr hkl) (h z hz))
    change dist ((z-u)/(v-u)) c=‖c‖ at hw
    have he : z-(u+(v-u)*c)=(v-u)*((z-u)/(v-u)-c) := by field_simp; ring
    rw [dist_eq_norm] at hw
    rw [dist_eq_norm,he,norm_mul,hw]

abbrev value (a b : ℂ[X]) (t : ℝ) : ℂ := a.eval (t : ℂ)/b.eval (t : ℂ)
def curve (a b : ℂ[X]) : Set ℂ :=
  value a b '' {t : ℝ | b.eval (t : ℂ)≠0}

lemma eval_bar_real (f : ℂ[X]) (t : ℝ) :
    (bar f).eval (t : ℂ)=starRingEnd ℂ (f.eval (t : ℂ)) := by
  simpa using eval_map_apply (starRingEnd ℂ) (p := f) (t : ℂ)

/-- Arbitrarily many symbolic square anchors force the entire real-parameter
rational-function image (excluding poles) onto a line or a circle. -/
theorem symbolic_square_anchors_line_or_circle {a b : ℂ[X]}
    (hab : IsCoprime a b) (hb : b≠0) (hW : wronskian a b≠0)
    (U : Set ℂ) (hU : U.Infinite)
    (hsq : ∀ u∈U, IsSquare (pencil a b u*bar (pencil a b u)*b*bar b)) :
    Collinear ℝ (curve a b) ∨ Cospherical (curve a b) := by
  obtain ⟨u,-,v,-,huv,k,l,hk,-,hu,hv⟩ := two_good_anchors hab hb hW U hU hsq
  apply line_or_circle_of_phase (curve a b) u v k l huv hk
  rintro z ⟨t,ht,rfl⟩
  have he (w m : ℂ) (hm : bar (pencil a b w)=C m*pencil a b w) :
      starRingEnd ℂ (a.eval (t : ℂ)-w*b.eval (t : ℂ))=
        m*(a.eval (t : ℂ)-w*b.eval (t : ℂ)) := by
    have hh := congrArg (fun f : ℂ[X] => f.eval (t : ℂ)) hm
    dsimp only at hh
    rw [eval_bar_real] at hh
    simpa only [pencil,eval_sub,eval_mul,eval_C] using hh
  exact phase_of_two_conjugates _ _ _ _ _ _ ht huv (he _ _ hu) (he _ _ hv)

lemma constant_pencil_curve {a b : ℂ[X]} (hab : IsCoprime a b)
    (hW : wronskian a b=0) : Collinear ℝ (curve a b) := by
  obtain ⟨ha,hb⟩ := hab.wronskian_eq_zero_iff.mp hW
  have heA := eq_C_of_derivative_eq_zero ha
  have heB := eq_C_of_derivative_eq_zero hb
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨a.coeff 0/b.coeff 0,(0 : ℂ),?_⟩
  rintro z ⟨t,-,rfl⟩
  refine ⟨0,?_⟩
  change a.eval (t : ℂ)/b.eval (t : ℂ)=_
  rw [heA,heB]
  simp

lemma square_cancel {f g : ℂ[X]} (hf : f≠0) (h : IsSquare (f^2*g)) : IsSquare g := by
  obtain ⟨r,hr⟩ := h
  have hd : f^2 ∣ r^2 := ⟨g,by simpa only [pow_two] using hr.symm⟩
  obtain ⟨q,hq⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : (2 : ℕ)≠0)).mp hd
  refine ⟨q,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hf)
  rw [hr,hq]
  ring

lemma common_factor_norm (a b g : ℂ[X]) (u : ℂ) :
    pencil (g*a) (g*b) u*bar (pencil (g*a) (g*b) u)*(g*b)*bar (g*b) =
      (g*bar g)^2*(pencil a b u*bar (pencil a b u)*b*bar b) := by
  simp only [pencil,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C]
  ring

lemma curve_common_factor_subset (a b g : ℂ[X]) : curve (g*a) (g*b) ⊆ curve a b := by
  rintro z ⟨t,ht,rfl⟩
  change (g*b).eval (t : ℂ)≠0 at ht
  rw [eval_mul] at ht
  have hg := (mul_ne_zero_iff.mp ht).1
  have hb := (mul_ne_zero_iff.mp ht).2
  refine ⟨t,hb,?_⟩
  simp only [value,eval_mul]
  exact (mul_div_mul_left _ _ hg).symm

/-- Removing common numerator/denominator factors does not require any extra
square assumption. The constant-map case is included. -/
theorem symbolic_square_anchors_line_or_circle_general (a b : ℂ[X]) (hb : b≠0)
    (U : Set ℂ) (hU : U.Infinite)
    (hsq : ∀ u∈U, IsSquare (pencil a b u*bar (pencil a b u)*b*bar b)) :
    Collinear ℝ (curve a b) ∨ Cospherical (curve a b) := by
  let g := gcd a b
  let A := a/g
  let B := b/g
  have hg : g≠0 := gcd_ne_zero_of_right hb
  have hA : g*A=a := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hB : g*B=b := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right _ _)
  have hB0 : B≠0 := right_div_gcd_ne_zero hb
  have hcop : IsCoprime A B := isCoprime_div_gcd_div_gcd hb
  have hsub : curve a b ⊆ curve A B := by
    rw [← hA,← hB]
    exact curve_common_factor_subset _ _ _
  by_cases hW : wronskian A B=0
  · exact Or.inl (Collinear.subset hsub (constant_pencil_curve hcop hW))
  have hnew : ∀ u∈U, IsSquare (pencil A B u*bar (pencil A B u)*B*bar B) := by
    intro u hu
    apply square_cancel (mul_ne_zero hg (Polynomial.map_ne_zero hg))
    rw [← common_factor_norm,hA,hB]
    exact hsq u hu
  rcases symbolic_square_anchors_line_or_circle hcop hB0 hW U hU hnew with h | h
  · exact Or.inl (Collinear.subset hsub h)
  · exact Or.inr (Cospherical.subset hsub h)

#print axioms symbolic_square_anchors_line_or_circle_general
#print axioms phase_circle
#print axioms line_or_circle_of_phase
#print axioms symbolic_square_anchors_line_or_circle
end
end Erdos213.RationalChordCircle
