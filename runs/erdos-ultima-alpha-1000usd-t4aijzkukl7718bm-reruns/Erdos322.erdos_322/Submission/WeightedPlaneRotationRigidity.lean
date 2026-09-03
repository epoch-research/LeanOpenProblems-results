import Submission.QuadraticDenominatorRigidity

/-! Rotation invariance for rational polynomial maps to quartic spheres,
using one binary source subform that is not inert at five. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev CircleAlgebra (d : ℤ) := Localization.Away (denominator d)
private abbrev polyMap (d : ℤ) : Polynomial ℚ →+* CircleAlgebra d :=
  algebraMap (Polynomial ℚ) (CircleAlgebra d)
private abbrev ratMap (d : ℤ) : ℚ →+* CircleAlgebra d := (polyMap d).comp Polynomial.C

private lemma polyMap_injective (d : ℤ) : Function.Injective (polyMap d) := by
  intro p q h
  obtain ⟨m,hm⟩ := IsLocalization.Away.exists_of_eq (denominator d) h
  exact mul_left_cancel₀ (pow_ne_zero m (denominator_monic d).ne_zero) hm

theorem circle_algebra_rigidity (d : ℤ) (hd : GoodFive d)
    (f : Fin 4 → CircleAlgebra d) (a : ℚ) (h : ∑ i, f i^4=ratMap d a) :
    ∃ b : Fin 4 → ℚ, ∀ i, f i=ratMap d (b i) := by
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (denominator d)) f
  choose P hP using hD
  obtain ⟨m,hm⟩ := D.property
  have hD' : (D : Polynomial ℚ)=denominator d^m := hm.symm
  have hPm (i : Fin 4) : polyMap d (P i)=polyMap d (denominator d^m)*f i := by
    simpa only [Algebra.smul_def,hD'] using hP i
  have hp : ∑ i, P i^4=C a*denominator d^(4*m) := by
    apply polyMap_injective d
    simp only [map_sum,map_pow,map_mul,hPm,mul_pow]
    rw [←Finset.mul_sum,h]
    change (polyMap d (denominator d)^m)^4*ratMap d a=
      ratMap d a*polyMap d (denominator d)^(4*m)
    rw [←pow_mul,mul_comm m 4,mul_comm]
  obtain ⟨b,hb⟩ := denominator_rigidity d hd P a m hp
  refine ⟨b,fun i ↦ ?_⟩
  have hi := hPm i
  rw [hb i,map_mul] at hi
  have hu : IsUnit (polyMap d (denominator d^m)) := by
    simpa only [map_pow] using
      IsLocalization.Away.algebraMap_pow_isUnit (denominator d) (S := CircleAlgebra d) m
  apply hu.mul_left_cancel
  change polyMap d (denominator d^m)*f i=polyMap d (denominator d^m)*polyMap d (C (b i))
  simpa only [mul_comm] using hi.symm

private def atParameter (d : ℤ) (hd : 0<d) (t : ℚ) : CircleAlgebra d →+* ℚ :=
  IsLocalization.Away.lift (denominator d) (g := Polynomial.evalRingHom t)
    (isUnit_iff_ne_zero.mpr (by
      change (denominator d).eval t ≠ 0
      have hp : (0 : ℚ)<d := by exact_mod_cast hd
      simp only [denominator,eval_add,eval_pow,eval_X,eval_C]
      positivity))

@[simp] private lemma atParameter_poly (d : ℤ) (hd : 0<d) (t : ℚ) (P : Polynomial ℚ) :
    atParameter d hd t (polyMap d P)=P.eval t :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] private lemma atParameter_rat (d : ℤ) (hd : 0<d) (t a : ℚ) :
    atParameter d hd t (ratMap d a)=a := by
  change atParameter d hd t (polyMap d (C a))=a
  simp

private def circleInv (d : ℤ) : CircleAlgebra d :=
  IsLocalization.Away.invSelf (denominator d)
private def circleCos (d : ℤ) : CircleAlgebra d :=
  polyMap d (C (d : ℚ)-X^2)*circleInv d
private def circleSin (d : ℤ) : CircleAlgebra d :=
  polyMap d (2*X)*circleInv d

private lemma circle_unit (d : ℤ) : circleCos d^2+ratMap d d*circleSin d^2=1 := by
  calc
    _ = (polyMap d (denominator d)*circleInv d)^2 := by
      simp only [circleCos,circleSin,denominator,map_sub,map_add,map_pow,map_mul,map_ofNat]
      change ((polyMap d (C (d : ℚ))-polyMap d X^2)*circleInv d)^2+
        polyMap d (C (d : ℚ))*(2*polyMap d X*circleInv d)^2=
        ((polyMap d X^2+polyMap d (C (d : ℚ)))*circleInv d)^2
      ring
    _ = 1 := by
      change (algebraMap (Polynomial ℚ) (CircleAlgebra d) (denominator d)*
        IsLocalization.Away.invSelf (denominator d))^2=1
      rw [IsLocalization.Away.mul_invSelf]
      simp

private lemma atParameter_inv (d : ℤ) (hd : 0<d) (t : ℚ) :
    atParameter d hd t (circleInv d)=1/(t^2+d) := by
  have hp : (0 : ℚ)<d := by exact_mod_cast hd
  apply (eq_div_iff (by positivity : t^2+(d : ℚ) ≠ 0)).mpr
  have he := congrArg (atParameter d hd t)
    (IsLocalization.Away.mul_invSelf (denominator d) (S := CircleAlgebra d))
  simpa [circleInv,denominator,mul_comm] using he

@[simp] private lemma atParameter_cos (d : ℤ) (hd : 0<d) (t : ℚ) :
    atParameter d hd t (circleCos d)=(d-t^2)/(d+t^2) := by
  simp [circleCos,atParameter_inv,div_eq_mul_inv,add_comm]

@[simp] private lemma atParameter_sin (d : ℤ) (hd : 0<d) (t : ℚ) :
    atParameter d hd t (circleSin d)=2*t/(d+t^2) := by
  simp [circleSin,atParameter_inv,div_eq_mul_inv,add_comm]

def weightedRotate {R : Type*} [CommRing R] (d : R) (x : Fin 3 → R) (c s : R) : Fin 3 → R :=
  ![c*x 0-d*s*x 1,s*x 0+c*x 1,x 2]

def sourceNorm {R : Type*} [CommRing R] (d e : R) (x : Fin 3 → R) : R :=
  x 0^2+d*x 1^2+e*x 2^2

lemma weightedRotate_norm {R : Type*} [CommRing R] (d e : R) (x : Fin 3 → R)
    (c s : R) (hcs : c^2+d*s^2=1) :
    sourceNorm d e (weightedRotate d x c s)=sourceNorm d e x := by
  dsimp [sourceNorm,weightedRotate]
  linear_combination (x 0^2+d*x 1^2)*hcs

@[simp] private lemma parameter_rotate (d : ℤ) (hd : 0<d) (x : Fin 3 → ℚ) (t : ℚ) :
    (fun l ↦ atParameter d hd t
      (weightedRotate (ratMap d d) (fun j ↦ ratMap d (x j)) (circleCos d) (circleSin d) l))=
      weightedRotate (d : ℚ) x ((d-t^2)/(d+t^2)) (2*t/(d+t^2)) := by
  funext l
  fin_cases l <;> simp [weightedRotate]

private lemma parameter_mv_eval (d : ℤ) (hd : 0<d) (P : MvPolynomial (Fin 3) ℚ)
    (x : Fin 3 → CircleAlgebra d) (t : ℚ) :
    atParameter d hd t (MvPolynomial.eval₂Hom (ratMap d) x P)=
      MvPolynomial.eval (fun l ↦ atParameter d hd t (x l)) P := by
  rw [MvPolynomial.map_eval₂Hom]
  have he : (atParameter d hd t).comp (ratMap d)=RingHom.id ℚ := by ext a; simp
  rw [he]
  rfl

/-- Rational weighted-plane rotations cannot change any output coordinate. -/
theorem rational_parameter_rotation_invariant (d : ℤ) (hd : 0<d) (hg : GoodFive d)
    (e : ℚ) (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X))
    (x : Fin 3 → ℚ) (t : ℚ) (l : Fin 4) :
    MvPolynomial.eval (weightedRotate (d : ℚ) x ((d-t^2)/(d+t^2)) (2*t/(d+t^2))) (P l)=
      MvPolynomial.eval x (P l) := by
  let y := weightedRotate (ratMap d d) (fun j ↦ ratMap d (x j)) (circleCos d) (circleSin d)
  let f : Fin 4 → CircleAlgebra d := fun i ↦ MvPolynomial.eval₂Hom (ratMap d) y (P i)
  have hy : sourceNorm (ratMap d d) (ratMap d e) y=ratMap d (sourceNorm (d : ℚ) e x) := by
    rw [weightedRotate_norm _ _ _ _ _ (circle_unit d)]
    simp [sourceNorm]
  have hf : ∑ i, f i^4=ratMap d (H.eval (sourceNorm (d : ℚ) e x)) := by
    have he := congrArg (MvPolynomial.eval₂Hom (ratMap d) y) h
    rw [Polynomial.hom_eval₂] at he
    have hm : (MvPolynomial.eval₂Hom (ratMap d) y).comp MvPolynomial.C=ratMap d := by
      ext a
      simp
    simp only [map_sum,map_pow,hm,sourceNorm,map_add,map_mul,
      MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X'] at he
    change (∑ i, f i^4)=H.eval₂ (ratMap d) (sourceNorm (ratMap d d) (ratMap d e) y) at he
    rw [hy,Polynomial.eval₂_at_apply] at he
    exact he
  obtain ⟨b,hb⟩ := circle_algebra_rigidity d hg f _ hf
  have hc : atParameter d hd t (f l)=atParameter d hd 0 (f l) := by rw [hb l]; simp
  dsimp only [f] at hc
  simp only [parameter_mv_eval] at hc
  dsimp only [y] at hc
  rw [parameter_rotate,parameter_rotate] at hc
  have hz : weightedRotate (d : ℚ) x ((d-(0 : ℚ)^2)/(d+0^2)) (2*0/(d+0^2))=x := by
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    funext j
    fin_cases j <;> simp [weightedRotate,hd0]
  simpa only [hz] using hc


/-- Real evaluation of a rational polynomial. -/
def realEval (P : MvPolynomial (Fin 3) ℚ) (x : Fin 3 → ℝ) : ℝ :=
  MvPolynomial.eval x (MvPolynomial.map (Rat.castHom ℝ) P)

private lemma realEval_cast (P : MvPolynomial (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    realEval P (fun j ↦ (x j : ℝ))=(MvPolynomial.eval x P : ℝ) := by
  have he := MvPolynomial.map_eval₂Hom (RingHom.id ℚ) x (Rat.castHom ℝ) P
  rw [realEval,←MvPolynomial.eval₂_eq_eval_map]
  simpa only [RingHom.comp_id,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_id] using he.symm

private lemma rotate_cast (d : ℤ) (x : Fin 3 → ℚ) (c s : ℚ) :
    weightedRotate (d : ℝ) (fun k ↦ (x k : ℝ)) (c : ℝ) (s : ℝ)=
      fun k ↦ ((weightedRotate (d : ℚ) x c s k : ℚ) : ℝ) := by
  funext k
  fin_cases k <;> simp [weightedRotate]

/-- The polynomial identity extends weighted rotation invariance to real inputs. -/
theorem real_parameter_rotation_invariant (d : ℤ) (hd : 0<d) (hg : GoodFive d)
    (e : ℚ) (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X))
    (x : Fin 3 → ℝ) (t : ℝ) (l : Fin 4) :
    realEval (P l) (weightedRotate (d : ℝ) x ((d-t^2)/(d+t^2)) (2*t/(d+t^2)))=
      realEval (P l) x := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  let F : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z ↦ realEval (P l)
    (weightedRotate (d : ℝ) z.1 ((d-z.2^2)/(d+z.2^2)) (2*z.2/(d+z.2^2)))
  let G : ((Fin 3 → ℝ) × ℝ) → ℝ := fun z ↦ realEval (P l) z.1
  have hF : Continuous F := by
    apply (MvPolynomial.continuous_eval (MvPolynomial.map (Rat.castHom ℝ) (P l))).comp
    apply continuous_pi
    intro k
    fin_cases k <;> dsimp [weightedRotate]
    all_goals fun_prop (disch := intro z; positivity)
  have hG : Continuous G :=
    (MvPolynomial.continuous_eval (MvPolynomial.map (Rat.castHom ℝ) (P l))).comp continuous_fst
  have hdense : DenseRange (fun z : (Fin 3 → ℚ) × ℚ ↦
      ((fun k ↦ (z.1 k : ℝ)),(z.2 : ℝ))) :=
    (DenseRange.piMap (fun _ : Fin 3 ↦ (Rat.denseRange_cast : DenseRange (Rat.cast : ℚ → ℝ)))).prodMap
      Rat.denseRange_cast
  have he : F=G := hdense.equalizer hF hG (by
    funext z
    rcases z with ⟨a,b⟩
    dsimp only [Function.comp_def,F,G]
    have hr := congrArg (Rat.cast : ℚ → ℝ)
      (rational_parameter_rotation_invariant d hd hg e P H h a b l)
    have hc : ((d : ℝ)-(b : ℝ)^2)/(d+(b : ℝ)^2)=
        ((((d : ℚ)-b^2)/(d+b^2) : ℚ) : ℝ) := by norm_cast
    have hs : 2*(b : ℝ)/(d+(b : ℝ)^2)=(((2*b/(d+b^2) : ℚ)) : ℝ) := by norm_cast
    rw [hc,hs,rotate_cast,realEval_cast,realEval_cast]
    exact hr)
  exact congrFun he (x,t)

private lemma real_rotation_nonexceptional (d : ℤ) (hd : 0<d) (hg : GoodFive d)
    (e : ℚ) (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X))
    (x : Fin 3 → ℝ) (c s : ℝ) (hcs : c^2+(d : ℝ)*s^2=1) (hc : c ≠ -1) (l : Fin 4) :
    realEval (P l) (weightedRotate (d : ℝ) x c s)=realEval (P l) x := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  let t : ℝ := (d : ℝ)*s/(1+c)
  have hc0 : 1+c ≠ 0 := by intro he; apply hc; linarith
  have ht0 : (d : ℝ)+t^2 ≠ 0 := by positivity
  have htC : ((d : ℝ)-t^2)/(d+t^2)=c := by
    apply (div_eq_iff ht0).mpr
    dsimp [t]
    field_simp
    linear_combination -(1+c)*hcs
  have htS : 2*t/(d+t^2)=s := by
    apply (div_eq_iff ht0).mpr
    dsimp [t]
    field_simp
    linear_combination -s*hcs
  simpa only [htC,htS] using real_parameter_rotation_invariant d hd hg e P H h x t l

/-- Includes the missing half-turn, hence every real weighted-plane rotation. -/
theorem real_rotation_invariant (d : ℤ) (hd : 0<d) (hg : GoodFive d)
    (e : ℚ) (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X))
    (x : Fin 3 → ℝ) (c s : ℝ) (hcs : c^2+(d : ℝ)*s^2=1) (l : Fin 4) :
    realEval (P l) (weightedRotate (d : ℝ) x c s)=realEval (P l) x := by
  by_cases hc : c=-1
  · have hdR : (0 : ℝ)<d := by exact_mod_cast hd
    have hs : s=0 := by
      have hh : (d : ℝ)*s^2=0 := by rw [hc] at hcs; nlinarith
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hdR))
    subst c; subst s
    let u : ℝ := 1/Real.sqrt (d : ℝ)
    have hroot : (Real.sqrt (d : ℝ))^2=(d : ℝ) := Real.sq_sqrt hdR.le
    have hroot0 : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdR)
    have hu : (d : ℝ)*u^2=1 := by dsimp [u]; field_simp; exact hroot.symm
    have hu' : (0 : ℝ)^2+(d : ℝ)*u^2=1 := by simpa using hu
    have h1 := real_rotation_nonexceptional d hd hg e P H h x 0 u hu' (by norm_num) l
    have h2 := real_rotation_nonexceptional d hd hg e P H h
      (weightedRotate (d : ℝ) x 0 u) 0 u hu' (by norm_num) l
    have hr : weightedRotate (d : ℝ) (weightedRotate (d : ℝ) x 0 u) 0 u=
        weightedRotate (d : ℝ) x (-1) 0 := by
      funext j
      fin_cases j <;> dsimp [weightedRotate]
      · linear_combination -x 0*hu
      · linear_combination -x 1*hu
    rw [hr] at h2
    exact h2.trans h1
  · exact real_rotation_nonexceptional d hd hg e P H h x c s hcs hc l

/-- One good binary subform suffices to move its two coordinates to an axis. -/
theorem axis_reduction (d : ℤ) (hd : 0<d) (hg : GoodFive d)
    (e : ℚ) (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X))
    (x : Fin 3 → ℝ) (l : Fin 4) :
    realEval (P l) ![Real.sqrt (x 0^2+(d : ℝ)*x 1^2),0,x 2]=realEval (P l) x := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  let r := Real.sqrt (x 0^2+(d : ℝ)*x 1^2)
  have hrs : r^2=x 0^2+(d : ℝ)*x 1^2 := Real.sq_sqrt (by positivity)
  by_cases hr : r=0
  · have h1 : x 1=0 := by
      have hh : (d : ℝ)*x 1^2=0 := by
        nlinarith [sq_nonneg (x 0),mul_nonneg hdR.le (sq_nonneg (x 1))]
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hdR))
    have h0 : x 0=0 := by nlinarith
    have hx : ![Real.sqrt (x 0^2+(d : ℝ)*x 1^2),0,x 2]=x := by
      funext j
      fin_cases j <;> simp [h0,h1]
    rw [hx]
  · have hcs : (x 0/r)^2+(d : ℝ)*(-x 1/r)^2=1 := by field_simp; exact hrs.symm
    have he : weightedRotate (d : ℝ) x (x 0/r) (-x 1/r)=![r,0,x 2] := by
      funext j
      fin_cases j <;> dsimp [weightedRotate]
      · field_simp; nlinarith [hrs]
      · ring
    have hh := real_rotation_invariant d hd hg e P H h x (x 0/r) (-x 1/r) hcs l
    rw [he] at hh
    exact hh

end
end Erdos322Research.QuadraticQuarticFive
