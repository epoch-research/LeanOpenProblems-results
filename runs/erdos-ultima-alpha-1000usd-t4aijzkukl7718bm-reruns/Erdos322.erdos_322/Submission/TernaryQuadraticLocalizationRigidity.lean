import Submission.DiagonalQuadraticPolynomialRigidity
import Submission.QuarticAutomaticHomogeneity

/-! Constant fourth-power norm over a localization at a positive ternary quadratic.
This is a construction theorem, not a bound on representation counts. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

abbrev TernaryPoly := MvPolynomial (Fin 3) ℚ

def ternaryDenom (d e : ℚ) : TernaryPoly :=
  MvPolynomial.X 0^2+MvPolynomial.C d*MvPolynomial.X 1^2+
    MvPolynomial.C e*MvPolynomial.X 2^2

@[simp] theorem eval_ternaryDenom (d e : ℚ) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x (ternaryDenom d e)=sourceNorm d e x := by
  simp [ternaryDenom,sourceNorm]

private abbrev firstAxis : TernaryPoly →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0]

private lemma axis_real_eval (P : TernaryPoly) (t : ℝ) :
    (firstAxis P).eval₂ (Rat.castHom ℝ) t=realEval P ![t,0,0] := by
  change Polynomial.eval₂RingHom (Rat.castHom ℝ) t (firstAxis P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.eval₂RingHom (Rat.castHom ℝ) t).comp Polynomial.C=Rat.castHom ℝ := by
    ext r
    simp
  have hx : (fun j : Fin 3 ↦ Polynomial.eval₂RingHom (Rat.castHom ℝ) t
      (![Polynomial.X,0,0] j))=![t,0,0] := by
    funext j
    fin_cases j <;> simp
  rw [hc,hx]
  rw [realEval,←MvPolynomial.eval₂_eq_eval_map]
  rfl

private lemma realEval_rat (P : TernaryPoly) (x : Fin 3 → ℚ) :
    realEval P (fun j ↦ (x j : ℝ))=(MvPolynomial.eval x P : ℝ) := by
  have he := MvPolynomial.map_eval₂Hom (RingHom.id ℚ) x (Rat.castHom ℝ) P
  rw [realEval,←MvPolynomial.eval₂_eq_eval_map]
  simpa only [RingHom.comp_id,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_id] using he.symm

/-- A fourth-power norm equal to a power of a positive ternary quadratic
forces each coordinate to be the corresponding radial power. -/
theorem ternary_denominator_polynomial_rigidity (d e : ℚ) (hd : 0<d) (he : 0<e)
    (P : Fin 4 → TernaryPoly) (c : ℚ) (m : ℕ)
    (h : ∑ i, P i^4=MvPolynomial.C c*ternaryDenom d e^(4*m)) :
    ∃ b : Fin 4 → ℚ, ∀ i, P i=MvPolynomial.C (b i)*ternaryDenom d e^m := by
  have haxis : ∑ i, (firstAxis (P i))^4=Polynomial.C c*Polynomial.X^(4*(2*m)) := by
    have hh := congrArg firstAxis h
    simpa [firstAxis,ternaryDenom,←pow_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh
  obtain ⟨b,hb⟩ := QuarticAutomaticHomogeneity.monomial_fourth_sum
    (fun i ↦ firstAxis (P i)) c (2*m) haxis
  refine ⟨b,fun i ↦ ?_⟩
  apply MvPolynomial.funext
  intro x
  let xr : Fin 3 → ℝ := fun j ↦ (x j : ℝ)
  let q : ℝ := sourceNorm (d : ℝ) (e : ℝ) xr
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have heR : (0 : ℝ)<e := by exact_mod_cast he
  have hq : 0≤q := by dsimp [q,sourceNorm]; positivity
  let t : ℝ := Real.sqrt q
  have ht : t^2=q := Real.sq_sqrt hq
  have hn : ∑ j, P j^4=(Polynomial.C c*Polynomial.X^(4*m)).eval₂ MvPolynomial.C
      (∑ j : Fin 3, MvPolynomial.C (![1,d,e] j)*MvPolynomial.X j^2) := by
    simpa [Fin.sum_univ_three,ternaryDenom] using h
  have hxy : (∑ j : Fin 3, ((![1,d,e] j : ℚ) : ℝ)*xr j^2)=
      ∑ j : Fin 3, ((![1,d,e] j : ℚ) : ℝ)*(![t,0,0] j)^2 := by
    simpa [Fin.sum_univ_three,q,sourceNorm] using ht.symm
  have hh := diagonal_constant_on_fibers ![1,d,e]
    (by intro j; fin_cases j; norm_num; exact hd; exact he)
    P (Polynomial.C c*Polynomial.X^(4*m)) hn xr ![t,0,0] hxy i
  have ha : realEval (P i) ![t,0,0]=(b i : ℝ)*q^m := by
    rw [←axis_real_eval,hb i]
    simp only [eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
    rw [pow_mul,ht]
    rfl
  rw [ha] at hh
  have hqr : q=(MvPolynomial.eval x (ternaryDenom d e) : ℝ) := by
    simp [q,sourceNorm,xr,ternaryDenom]
  rw [hqr] at hh
  change realEval (P i) (fun j ↦ (x j : ℝ))=_ at hh
  rw [realEval_rat] at hh
  have hc : (MvPolynomial.eval x (MvPolynomial.C (b i)*ternaryDenom d e^m) : ℝ)=
      (b i : ℝ)*(MvPolynomial.eval x (ternaryDenom d e) : ℝ)^m := by simp
  exact_mod_cast hh.trans hc.symm

lemma ternaryDenom_ne_zero (d e : ℚ) : ternaryDenom d e ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (![1,0,0] : Fin 3 → ℚ)) h
  norm_num [ternaryDenom,Matrix.cons_val_two] at hh

abbrev TernaryAway (d e : ℚ) := Localization.Away (ternaryDenom d e)
abbrev ternaryPolyMap (d e : ℚ) : TernaryPoly →+* TernaryAway d e :=
  algebraMap TernaryPoly (TernaryAway d e)
abbrev ternaryRatMap (d e : ℚ) : ℚ →+* TernaryAway d e :=
  (ternaryPolyMap d e).comp MvPolynomial.C

lemma ternaryPolyMap_injective (d e : ℚ) : Function.Injective (ternaryPolyMap d e) := by
  intro p q h
  obtain ⟨m,hm⟩ := IsLocalization.Away.exists_of_eq (ternaryDenom d e) h
  exact mul_left_cancel₀ (pow_ne_zero m (ternaryDenom_ne_zero d e)) hm

/-- Four rational functions with only powers of this ternary quadratic as
possible denominators cannot have a nonconstant constant-quartic-norm map. -/
theorem ternary_localization_rigidity (d e : ℚ) (hd : 0<d) (he : 0<e)
    (f : Fin 4 → TernaryAway d e) (c : ℚ)
    (h : ∑ i, f i^4=ternaryRatMap d e c) :
    ∃ b : Fin 4 → ℚ, ∀ i, f i=ternaryRatMap d e (b i) := by
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (ternaryDenom d e)) f
  choose P hP using hD
  obtain ⟨m,hm⟩ := D.property
  have hD' : (D : TernaryPoly)=ternaryDenom d e^m := hm.symm
  have hPm (i : Fin 4) : ternaryPolyMap d e (P i)=
      ternaryPolyMap d e (ternaryDenom d e^m)*f i := by
    simpa only [Algebra.smul_def,hD'] using hP i
  have hp : ∑ i, P i^4=MvPolynomial.C c*ternaryDenom d e^(4*m) := by
    apply ternaryPolyMap_injective d e
    simp only [map_sum,map_pow,map_mul,hPm,mul_pow]
    rw [←Finset.mul_sum,h]
    change (ternaryPolyMap d e (ternaryDenom d e)^m)^4*ternaryRatMap d e c=
      ternaryRatMap d e c*ternaryPolyMap d e (ternaryDenom d e)^(4*m)
    rw [←pow_mul,mul_comm m 4,mul_comm]
  obtain ⟨b,hb⟩ := ternary_denominator_polynomial_rigidity d e hd he P c m hp
  refine ⟨b,fun i ↦ ?_⟩
  have hi := hPm i
  rw [hb i,map_mul] at hi
  have hu : IsUnit (ternaryPolyMap d e (ternaryDenom d e^m)) := by
    simpa only [map_pow] using
      IsLocalization.Away.algebraMap_pow_isUnit (ternaryDenom d e) (S := TernaryAway d e) m
  apply hu.mul_left_cancel
  change ternaryPolyMap d e (ternaryDenom d e^m)*f i=
    ternaryPolyMap d e (ternaryDenom d e^m)*ternaryPolyMap d e (MvPolynomial.C (b i))
  simpa only [mul_comm] using hi.symm

def ternaryAt (d e : ℚ) (x : Fin 3 → ℚ) (hx : sourceNorm d e x ≠ 0) :
    TernaryAway d e →+* ℚ :=
  IsLocalization.Away.lift (ternaryDenom d e) (g := MvPolynomial.eval x)
    (isUnit_iff_ne_zero.mpr (by simpa using hx))

@[simp] lemma ternaryAt_poly (d e : ℚ) (x : Fin 3 → ℚ)
    (hx : sourceNorm d e x ≠ 0) (p : TernaryPoly) :
    ternaryAt d e x hx (ternaryPolyMap d e p)=MvPolynomial.eval x p :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] lemma ternaryAt_rat (d e : ℚ) (x : Fin 3 → ℚ)
    (hx : sourceNorm d e x ≠ 0) (r : ℚ) :
    ternaryAt d e x hx (ternaryRatMap d e r)=r := by
  change ternaryAt d e x hx (ternaryPolyMap d e (MvPolynomial.C r))=r
  simp

/-- Evaluation away from the denominator zero separates elements of this localization. -/
theorem ternaryAway_ext (d e : ℚ) (hd : 0<d) (he : 0<e)
    (f g : TernaryAway d e)
    (h : ∀ (x : Fin 3 → ℚ) (hx : sourceNorm d e x ≠ 0),
      ternaryAt d e x hx f=ternaryAt d e x hx g) : f=g := by
  obtain ⟨m,P,hP⟩ := IsLocalization.Away.surj (ternaryDenom d e) (f-g)
  have hp0 : P=0 := by
    apply MvPolynomial.funext_set (fun _ : Fin 3 ↦ Set.Ioi (0 : ℚ))
      (fun _ ↦ Set.Ioi_infinite 0)
    intro x hx
    have hx0 : 0<x 0 := hx 0 (Set.mem_univ _)
    have hq : sourceNorm d e x ≠ 0 := by
      have hp : 0<x 0^2 := sq_pos_of_pos hx0
      dsimp only [sourceNorm]
      positivity
    have hh := congrArg (ternaryAt d e x hq) hP
    simp only [map_mul,map_sub,map_pow,ternaryAt_poly,h x hq,sub_self,zero_mul] at hh
    simpa using hh.symm
  have hz : (f-g)*ternaryPolyMap d e (ternaryDenom d e)^m=0 := by
    simpa only [hp0,map_zero] using hP
  have hu := IsLocalization.Away.algebraMap_pow_isUnit
    (ternaryDenom d e) (S := TernaryAway d e) m
  apply sub_eq_zero.mp
  exact hu.mul_right_cancel (by simpa using hz)

end
end Erdos322Research.QuadraticQuarticFive
