import Submission.CollisionMotion

/-! Algebra for a two-point splitting investigation. The square hypothesis is
an identity in a rational-function field, not a square at one specialization.
This file does not settle Erdős 213 or give a complete splitting classification. -/
namespace Erdos213.GeneralQuadraticType
open Polynomial CircleLineRigidity QuadraticMotion
noncomputable section
set_option maxHeartbeats 2000000

/-- For arbitrary complex initial position, the nonrepeated-root branch has a
fixed complex direction. The leading coefficient is allowed to vanish. -/
lemma quadratic_type (a b c : ℂ) (ha : a ≠ 0)
    (hsq : IsSquare (quad c b a*(quad c b a).map (starRingEnd ℂ))) :
    b^2-4*a*c=0 ∨ (cross a b=0 ∧ cross a c=0) := by
  by_cases hd : b^2-4*a*c=0
  · exact Or.inl hd
  right
  have hd' : b^2-4*c*a≠0 := by convert hd using 1; ring
  have hf : quad c b a ≠ 0 := by
    intro h
    have hz := congrArg (fun p : ℂ[X] => p.coeff 0) h
    exact ha (by simpa only [quad_coeff_zero,coeff_zero] using hz)
  obtain ⟨q,hq⟩ := squarefree_dvd_partner hf (quad_separable c b a hd').squarefree hsq
  have hg : (quad c b a).map (starRingEnd ℂ)≠0 := by simpa using hf
  have hq0 : q≠0 := by intro h; apply hg; simp [hq,h]
  have hdeg := congrArg (fun p : ℂ[X] => p.natDegree) hq
  change ((quad c b a).map (starRingEnd ℂ)).natDegree=((quad c b a)*q).natDegree at hdeg
  rw [natDegree_map_eq_of_injective (starRingEnd ℂ).injective,natDegree_mul hf hq0] at hdeg
  have hn : q.natDegree=0 := by omega
  rw [eq_C_of_natDegree_eq_zero hn] at hq
  have h0 := congrArg (fun p : ℂ[X] => p.coeff 0) hq
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hq
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) hq
  simp only [coeff_map,coeff_mul_C,quad_coeff_zero,quad_coeff_one,quad_coeff_two] at h0 h1 h2
  have hb : a*(starRingEnd ℂ b)-b*(starRingEnd ℂ a)=0 := by rw [h0,h1]; ring
  have hc : a*(starRingEnd ℂ c)-c*(starRingEnd ℂ a)=0 := by rw [h0,h2]; ring
  have hbi := congrArg Complex.im hb
  have hci := congrArg Complex.im hc
  simp only [Complex.sub_im,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.zero_im] at hbi hci
  dsimp [cross]
  constructor <;> linarith

def squaredNorm (a b c : ℂ) : ℝ[X] :=
  (quad c.re b.re a.re)^2+(quad c.im b.im a.im)^2

lemma quadratic_type_ratFunc (a b c : ℂ) (ha : a ≠ 0)
    (hsq : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a b c))) :
    b^2-4*a*c=0 ∨ (cross a b=0 ∧ cross a c=0) := by
  apply quadratic_type a b c ha
  rw [quad_map,quad_conjugate_product]
  obtain ⟨p,hp⟩ := polynomial_square_of_ratFunc_square _ hsq
  refine ⟨p.map (algebraMap ℝ ℂ),?_⟩
  simpa [squaredNorm,map_mul] using congrArg (Polynomial.map (algebraMap ℝ ℂ)) hp

lemma constant_direction (a b c : ℂ) (ha : a≠0)
    (hb : cross a b=0) (hc : cross a c=0) :
    ∃ u v : ℝ, ∀ t : ℝ, a+b*t+c*t^2 = (1+u*t+v*t^2 : ℝ)*a := by
  obtain ⟨u,hu⟩ := (cross_zero_iff_real_mul ha).mp hb
  obtain ⟨v,hv⟩ := (cross_zero_iff_real_mul ha).mp hc
  refine ⟨u,v,?_⟩
  intro t
  rw [hu,hv]
  push_cast
  ring

/-- In the repeated-root branch the polynomial itself is a constant times a
square of a complex affine polynomial. -/
lemma repeated_root_form (a b c : ℂ) (ha : a≠0) (h : b^2-4*a*c=0) (t : ℝ) :
    a+b*t+c*t^2 = a*(1+(b/(2*a))*t)^2 := by
  field_simp
  linear_combination -(t : ℂ)^2*h

lemma squaredNorm_eval (a b c : ℂ) (t : ℝ) :
    (squaredNorm a b c).eval t = ‖a+b*t+c*t^2‖^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [squaredNorm,quad,pow_two,Complex.mul_re,Complex.mul_im]
  ring

lemma radial_against_one (a b c : ℂ) (hai : a.im≠0)
    (hb : cross a b=0) (hc : cross a c=0)
    (hd : (b-1)^2-4*a*c=0) :
    b=((a⁻¹).re : ℂ)*a ∧ c=(-((a⁻¹).im)^2/4 : ℝ)*a := by
  have ha : a≠0 := fun h => hai (by simp [h])
  have hy : (a⁻¹).im≠0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hai) (ne_of_gt (Complex.normSq_pos.mpr ha))
  obtain ⟨l,hl⟩ := (cross_zero_iff_real_mul ha).mp hb
  obtain ⟨m,hm⟩ := (cross_zero_iff_real_mul ha).mp hc
  rw [hl,hm] at hd
  have he : ((l : ℂ)-a⁻¹)^2-4*(m : ℂ)=0 := by
    field_simp
    linear_combination hd
  have hi := congrArg Complex.im he
  have hr := congrArg Complex.re he
  simp only [pow_two,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,
    Complex.zero_re,Complex.zero_im] at hi hr
  simp only [Complex.re_ofNat,Complex.im_ofNat] at hi hr
  have hf : (a⁻¹).im*(l-(a⁻¹).re)=0 := by linear_combination -hi/2
  have hl' : l=(a⁻¹).re := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hy)
  have hm' : m=-((a⁻¹).im)^2/4 := by rw [hl'] at hr; nlinarith only [hr]
  simpa only [hl',hm'] using And.intro hl hm

/-- Complete coefficient normal form relative to the normalized splitting
anchors `0` and `t`, for a nonreal initial point. The three branches are
usually called left-radial, right-radial, and double-repeated-root. -/
theorem two_anchor_normal_form (a b c : ℂ) (hai : a.im≠0)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a b c)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (squaredNorm a (b-1) c))) :
    (b=((a⁻¹).re : ℂ)*a ∧ c=(-((a⁻¹).im)^2/4 : ℝ)*a) ∨
    (b=1-((a⁻¹).re : ℂ)*a ∧ c=(-((a⁻¹).im)^2/4 : ℝ)*a) ∨
    (b=1/2 ∧ c=1/(16*a)) := by
  have ha : a≠0 := fun h => hai (by simp [h])
  rcases quadratic_type_ratFunc a b c ha h0 with hd0 | ⟨hb0,hc0⟩
  · rcases quadratic_type_ratFunc a (b-1) c ha h1 with hd1 | ⟨hb1,hc1⟩
    · right; right
      have hb : b=1/2 := by linear_combination (hd0-hd1)/2
      refine ⟨hb,?_⟩
      rw [hb] at hd0
      field_simp
      linear_combination -4*hd0
    · right; left
      have hh := radial_against_one (-a) (1-b) (-c) (by simpa using hai)
        (by dsimp [cross] at hb1 ⊢; linear_combination hb1)
        (by simpa [cross] using hc1)
        (by linear_combination hd0)
      simp only [inv_neg,Complex.neg_re,Complex.neg_im,neg_sq] at hh
      push_cast at hh ⊢
      constructor
      · linear_combination -hh.1
      · linear_combination -hh.2
  · rcases quadratic_type_ratFunc a (b-1) c ha h1 with hd1 | ⟨hb1,_⟩
    · exact Or.inl (radial_against_one a b c hai hb0 hc0 hd1)
    · exfalso
      apply hai
      dsimp [cross] at hb0 hb1
      linear_combination hb1-hb0

/-- A nonzero real initial point remains on the splitting-anchor line.
This handles the real-initial-position exception to the three-type form. -/
lemma real_initial_coefficients (a : ℝ) (ha : a≠0) (b c : ℂ)
    (h0 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (QuadraticMotion.normPolynomial a b c)))
    (h1 : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (QuadraticMotion.normPolynomial a (b-1) c))) :
    b.im=0 ∧ c.im=0 := by
  have ht0 := QuadraticMotion.quadratic_type_ratFunc a b c ha h0
  have ht1 := QuadraticMotion.quadratic_type_ratFunc a (b-1) c ha h1
  have hb : b.im=0 := by
    rcases ht0 with hd0 | hh0
    · rcases ht1 with hd1 | hh1
      · have he : b=1/2 := by linear_combination (hd0-hd1)/2
        rw [he]
        norm_num
      · simpa using hh1.1
    · exact hh0.1
  exact ⟨hb,QuadraticMotion.quadratic_imag_zero a b c ha ht0 hb⟩

#print axioms real_initial_coefficients
#print axioms two_anchor_normal_form
#print axioms quadratic_type_ratFunc
#print axioms constant_direction
#print axioms repeated_root_form
end
end Erdos213.GeneralQuadraticType
