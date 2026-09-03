import Submission.MedianFamily

/-! Three exact genus-two cover conditions for the conditional median family,
and descent of a real parameter with rational reciprocal/shape data.
No nondegenerate rational point or unconditional cardinality claim is made. -/
namespace Erdos213.MedianCoverDescent
open MedianFamily Polynomial
set_option maxHeartbeats 1000000

def minusCover (u : ℚ) : ℚ := (u-6)*quotientPolynomial u
def plusCover (u : ℚ) : ℚ := (u+6)*quotientPolynomial u
def productCover (u : ℚ) : ℚ := (u-6)*(u+6)*quotientPolynomial u

lemma quotient_ne_zero (u : ℚ) : quotientPolynomial u≠0 := by
  let p : ℤ[X] := X^4-76*X^3+1920*X^2+29360*X+31984
  have hp : p.Monic := by dsimp [p]; monicity!
  have hm : ∀ x : ZMod 5, p.eval₂ (Int.castRingHom _) x≠0 := by
    simp only [p,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_ofNat]
    decide
  intro hu
  have he : Polynomial.aeval u p=0 := by
    simpa [p,quotientPolynomial,Polynomial.aeval_def] using hu
  obtain ⟨z,hz,_⟩ := exists_integer_of_is_root_of_monic hp he
  have hZ : p.eval z=0 := by
    apply IsFractionRing.injective ℤ ℚ
    simpa [hz,Polynomial.aeval_def,Polynomial.eval₂_at_apply] using he
  apply hm (z : ZMod 5)
  change p.eval₂ (Int.castRingHom (ZMod 5)) ((Int.castRingHom (ZMod 5)) z)=0
  rw [Polynomial.eval₂_at_apply,hZ,map_zero]

lemma covers_away {u : ℚ} (hm : IsSquare (minusCover u))
    (hp : IsSquare (plusCover u)) : u≠6 ∧ u≠-6 := by
  constructor
  · rintro rfl
    norm_num [plusCover,quotientPolynomial] at hp
  · rintro rfl
    norm_num [minusCover,quotientPolynomial] at hm

/-- All three covers together recover the three original square classes.
Membership in only one or two quotient curves is insufficient. -/
lemma three_covers_iff (u : ℚ) :
    (IsSquare (minusCover u) ∧ IsSquare (plusCover u) ∧ IsSquare (productCover u)) ↔
      IsSquare (quotientPolynomial u) ∧ IsSquare (u-6) ∧ IsSquare (u+6) := by
  constructor
  · rintro ⟨hm,hp,hb⟩
    obtain ⟨hu6,hu6'⟩ := covers_away hm hp
    have hminus : u-6≠0 := sub_ne_zero.mpr hu6
    have hplus : u+6≠0 := by intro h; apply hu6'; linarith
    have hP := quotient_ne_zero u
    refine ⟨?_,?_,?_⟩
    · convert (hm.mul hp).div hb using 1
      unfold minusCover plusCover productCover
      field_simp
    · convert hb.div hp using 1
      unfold productCover plusCover
      field_simp
    · convert hb.div hm using 1
      unfold productCover minusCover
      field_simp
  · rintro ⟨hP,hm,hp⟩
    exact ⟨hm.mul hP,hp.mul hP,(hm.mul hp).mul hP⟩

/-- Complete arithmetic equivalence with the original genus-seven parameter.
It has no existence assertion: the only known lifts remain degenerate. -/
theorem three_covers_parameter_iff (u : ℚ) :
    (IsSquare (minusCover u) ∧ IsSquare (plusCover u) ∧ IsSquare (productCover u)) ↔
      ∃ r : ℚ, r≠0 ∧ u=r^2+9/r^2 ∧ IsSquare (extraPolynomial r) := by
  rw [three_covers_iff]
  constructor
  · rintro ⟨hP,hm,hp⟩
    obtain ⟨r,hr,hu⟩ := (reciprocal_parameter_iff u).mpr ⟨hm,hp⟩
    refine ⟨r,hr,hu,(quotient_square_iff hr).mpr ?_⟩
    rwa [← hu]
  · rintro ⟨r,hr,rfl,hF⟩
    exact ⟨(quotient_square_iff hr).mp hF,
      (reciprocal_parameter_iff _).mp ⟨r,hr,rfl⟩⟩

lemma positive_quotient_control :
    22<(70 : ℚ) ∧ quotientPolynomial (70 : ℚ)=3072^2 ∧
    minusCover (70 : ℚ)=24576^2 ∧ IsSquare ((70 : ℚ)-6) ∧
    ¬IsSquare ((70 : ℚ)+6) := by
  norm_num [quotientPolynomial,minusCover]

lemma two_cover_control :
    plusCover (22 : ℚ)=5376^2 ∧ productCover (22 : ℚ)=21504^2 ∧
    ¬IsSquare (minusCover (22 : ℚ)) := by
  norm_num [plusCover,productCover,minusCover,quotientPolynomial]

/-- Real versions of the degree-five side polynomials. -/
def realA (r : ℝ) : ℝ := r^5+r^4-6*r^3+26*r^2+9*r+9
def realB (r : ℝ) : ℝ := 6*r^4+20*r^2-18
def realC (r : ℝ) : ℝ := r^5-r^4-6*r^3-26*r^2+9*r-9
def realMedianU (r : ℝ) : ℝ := r^5+3*r^4+26*r^3-18*r^2+9*r+27

lemma real_shape_reduction {r u : ℝ} (h : r^4-u*r^2+9=0) :
    realA r=r^2*(r*(u-6)+u+26) ∧
    realB r=2*r^2*(4*r^2-u+10) ∧
    realC r=r^2*(r*(u-6)-u-26) := by
  unfold realA realB realC
  refine ⟨?_,?_,?_⟩
  · linear_combination (r+1)*h
  · linear_combination -2*h
  · linear_combination (r-1)*h

lemma denominator_reduction {r u : ℝ} (h : r^4-u*r^2+9=0) :
    (4*r^2-u+10)^2=8*(u+10)*r^2+u^2-20*u-44 := by
  linear_combination 16*h

lemma normalized_sum_relation {r u S : ℝ} (hr : r≠0)
    (h : r^4-u*r^2+9=0) (hs : (realA r)^2+(realC r)^2=S*(realB r)^2) :
    2*S*(8*(u+10)*r^2+u^2-20*u-44)=r^2*(u-6)^2+(u+26)^2 := by
  obtain ⟨ha,hb,hc⟩ := real_shape_reduction h
  rw [ha,hb,hc] at hs
  have hd := denominator_reduction h
  have he : r^4*(2*S*(8*(u+10)*r^2+u^2-20*u-44)-
      r^2*(u-6)^2-(u+26)^2)=0 := by
    linear_combination (-1/2 : ℝ)*hs-2*S*r^4*hd
  have hz := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 4 hr)
  linarith

lemma normalized_difference_relation {r u K : ℝ} (hr : r≠0)
    (h : r^4-u*r^2+9=0) (hs : (realA r)^2-(realC r)^2=K*(realB r)^2) :
    r*(u-6)*(u+26)=K*(4*r^2-u+10)^2 := by
  obtain ⟨ha,hb,hc⟩ := real_shape_reduction h
  rw [ha,hb,hc] at hs
  have he : r^4*(r*(u-6)*(u+26)-K*(4*r^2-u+10)^2)=0 := by
    linear_combination (1/4 : ℝ)*hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero 4 hr))

def mobiusDet (u : ℚ) : ℚ := (u^2-44*u-284)*(u^2+4*u+196)
def recoverDen (u S : ℚ) : ℚ := 16*S*(u+10)-(u-6)^2
def recoverNum (u S : ℚ) : ℚ := (u+26)^2-2*S*(u^2-20*u-44)

lemma mobius_det_ne (u : ℚ) : mobiusDet u≠0 := by
  unfold mobiusDet
  apply mul_ne_zero
  · intro h
    have hs : ((u-22)/16)^2=3 := by nlinarith only [h]
    have hn : ¬IsSquare (3 : ℚ) := by norm_num
    exact hn ⟨(u-22)/16,by nlinarith only [hs]⟩
  · have h : 0<u^2+4*u+196 := by nlinarith [sq_nonneg (u+2)]
    exact ne_of_gt h

lemma recovery_identity (u S : ℚ) :
    recoverDen u S*(u^2-20*u-44)+8*(u+10)*recoverNum u S = -mobiusDet u := by
  unfold recoverDen recoverNum mobiusDet
  ring

/-- The side-square sum determines r^2 over Q whenever the reciprocal parameter
is rational. The potential Mobius determinant zeros are not rational. -/
lemma square_parameter_rational {r : ℝ} {u S : ℚ} (hr : r≠0)
    (h : r^4-(u : ℝ)*r^2+9=0)
    (hs : (realA r)^2+(realC r)^2=(S : ℝ)*(realB r)^2) :
    ∃ z : ℚ, r^2=(z : ℝ) := by
  have he := normalized_sum_relation hr h hs
  have hlin : (recoverDen u S : ℝ)*r^2=(recoverNum u S : ℝ) := by
    unfold recoverDen recoverNum
    push_cast
    linear_combination he
  have hd : recoverDen u S≠0 := by
    intro hd
    have hnR : (recoverNum u S : ℝ)=0 := by rw [hd] at hlin; simpa using hlin.symm
    have hn : recoverNum u S=0 := by exact_mod_cast hnR
    have hi := recovery_identity u S
    rw [hd,hn] at hi
    exact mobius_det_ne u (by linarith only [hi])
  refine ⟨recoverNum u S/recoverDen u S,?_⟩
  push_cast
  exact (eq_div_iff (by exact_mod_cast hd)).mpr (by simpa only [mul_comm] using hlin)

lemma reciprocal_lower_bound {r : ℝ} {u : ℚ} (hr : r≠0)
    (h : r^4-(u : ℝ)*r^2+9=0) : (6 : ℚ)≤u := by
  have hp : 0<r^2 := sq_pos_of_ne_zero hr
  have hh : 0≤((u : ℝ)-6)*r^2 := by nlinarith [sq_nonneg (r^2-3)]
  have hu : (6 : ℝ)≤u := by nlinarith only [hp,hh]
  exact_mod_cast hu

/-- Allowing real algebraic parameters above a rational quotient gives no new
rational shape parameters, except the r^2=3 equilateral specialization. -/
theorem real_parameter_descent {r : ℝ} {u A C : ℚ} (hr : r≠0)
    (h : r^4-(u : ℝ)*r^2+9=0)
    (hA : (realA r)^2=(A : ℝ)*(realB r)^2)
    (hC : (realC r)^2=(C : ℝ)*(realB r)^2) :
    r^2=3 ∨ r∈Set.range ((↑) : ℚ → ℝ) := by
  by_cases hu : u=6
  · left
    rw [hu] at h
    norm_num at h
    nlinarith only [h,sq_nonneg (r^2-3)]
  right
  have hs : (realA r)^2+(realC r)^2=((A+C : ℚ) : ℝ)*(realB r)^2 := by
    push_cast
    linear_combination hA+hC
  obtain ⟨z,hz⟩ := square_parameter_rational hr h hs
  have hd : (realA r)^2-(realC r)^2=((A-C : ℚ) : ℝ)*(realB r)^2 := by
    push_cast
    linear_combination hA-hC
  have he := normalized_difference_relation hr h hd
  have h6 : u-6≠0 := sub_ne_zero.mpr hu
  have h26 : u+26≠0 := by have hh := reciprocal_lower_bound hr h; linarith
  have hden : ((u : ℝ)-6)*((u : ℝ)+26)≠0 := by exact_mod_cast mul_ne_zero h6 h26
  refine ⟨(A-C)*(4*z-u+10)^2/((u-6)*(u+26)),?_⟩
  push_cast
  apply (div_eq_iff hden).mpr
  rw [← hz]
  push_cast at he
  linear_combination -he

/-- One rational normalized median excludes the exceptional r^2=3 branch.
Thus this relaxation cannot supply a hidden irrational-parameter witness. -/
theorem rational_parameter_of_rational_shape_and_median {r : ℝ} {u A C M : ℚ}
    (hr : r≠0) (h : r^4-(u : ℝ)*r^2+9=0)
    (hA : (realA r)^2=(A : ℝ)*(realB r)^2)
    (hC : (realC r)^2=(C : ℝ)*(realB r)^2)
    (hM : (realMedianU r)^2=(M : ℝ)^2*(realB r)^2) :
    r∈Set.range ((↑) : ℚ → ℝ) := by
  rcases real_parameter_descent hr h hA hC with he | he
  · have hb : realB r=96 := by
      unfold realB
      linear_combination (6*r^2+38)*he
    have hm : realMedianU r=96*r := by
      unfold realMedianU
      linear_combination (r^3+3*r^2+29*r-9)*he
    rw [hb,hm] at hM
    have hsR : (M : ℝ)^2=3 := by nlinarith only [he,hM]
    have hs : M^2=3 := by exact_mod_cast hsR
    have hn : ¬IsSquare (3 : ℚ) := by norm_num
    exact False.elim (hn ⟨M,by nlinarith only [hs]⟩)
  · exact he

/-- A concrete partial quotient lift has irrational real parameters and cannot
be silently used as a rational parameter witness. -/
lemma seventy_branch {r : ℝ} (h : r^2-8*r-3=0) :
    r^4-70*r^2+9=0 ∧ realC r=realB r ∧
    17*realA r=(4*r-9)*realB r ∧ r∉Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (r^2+8*r-3)*h
  · unfold realC realB
    linear_combination (r^3+r^2+5*r-3)*h
  · unfold realA realB
    linear_combination (-7*r^3+15*r^2-83*r+3)*h
  · rintro ⟨q,hq⟩
    rw [← hq] at h
    have hh : (q-4)^2=19 := by
      have he : q^2-8*q-3=0 := by exact_mod_cast h
      nlinarith only [he]
    have hn : ¬IsSquare (19 : ℚ) := by norm_num
    exact hn ⟨q-4,by nlinarith only [hh]⟩

#print axioms seventy_branch
#print axioms quotient_ne_zero
#print axioms three_covers_parameter_iff
#print axioms positive_quotient_control
#print axioms two_cover_control
#print axioms square_parameter_rational
#print axioms real_parameter_descent
#print axioms rational_parameter_of_rational_shape_and_median
end Erdos213.MedianCoverDescent
