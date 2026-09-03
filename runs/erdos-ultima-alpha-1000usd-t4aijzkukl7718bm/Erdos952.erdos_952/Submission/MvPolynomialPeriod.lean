import Submission.MvPolynomialTranslation
import Submission.GaussianQuadraticCurveGeometry

/-! A real plane polynomial invariant under a nonzero translation has its
Gaussian zero set in a finite union of proper parallel affine lines. -/
namespace Erdos952Investigation.MvPolynomialPeriod
open MvPolynomial MvPolynomialTranslation GaussianQuadraticCurveGeometry
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

variable {σ : Type*}

def lineRestriction (p : MvPolynomial σ ℝ) (z d : σ → ℝ) : Polynomial ℝ :=
  eval₂Hom Polynomial.C (fun i => Polynomial.C (z i)+Polynomial.C (d i)*Polynomial.X) p

lemma eval_lineRestriction (p : MvPolynomial σ ℝ) (z d : σ → ℝ) (t : ℝ) :
    (lineRestriction p z d).eval t = eval (fun i => z i+d i*t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestriction]
  | add p q hp hq => simpa [lineRestriction] using congrArg₂ (·+·) hp hq
  | mul_X p i hp => simpa [lineRestriction] using congrArg (·*(z i+d i*t)) hp

/-- In characteristic zero, invariance under one step implies invariance
under every real multiple of that step. -/
lemma period_all_multiples (p : MvPolynomial σ ℝ) (d : σ → ℝ)
    (h : translate d p = p) (z : σ → ℝ) (t : ℝ) :
    eval (fun i => z i+d i*t) p = eval z p := by
  have hstep (w : σ → ℝ) : eval (fun i => w i+d i) p = eval w p := by
    rw [← eval_translate,h]
  have hn (n : ℕ) : eval (fun i => z i+d i*(n : ℝ)) p = eval z p := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he : (fun i => z i+d i*(n+1 : ℕ)) = (fun i => (z i+d i*(n : ℝ))+d i) := by
        funext i
        push_cast
        ring
      rw [he,hstep,ih]
  have hconst : lineRestriction p z d = Polynomial.C (eval z p) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℝ))).mono
    rintro v ⟨n,rfl⟩
    simpa only [Set.mem_setOf_eq,eval_lineRestriction,Polynomial.eval_C] using hn n
  have ht := congrArg (Polynomial.eval t) hconst
  simpa only [eval_lineRestriction,Polynomial.eval_C] using ht

abbrev PlanePoly := MvPolynomial (Fin 2) ℝ

def coords (z : GaussianInt) : Fin 2 → ℝ := ![(z.re : ℝ),(z.im : ℝ)]
def evalG (p : PlanePoly) (z : GaussianInt) : ℝ := eval (coords z) p

def shift (d : GaussianInt) : PlanePoly →+* PlanePoly := translate (coords d)

lemma evalG_shift (p : PlanePoly) (z d : GaussianInt) :
    evalG (shift d p) z = evalG p (z+d) := by
  unfold evalG shift
  rw [eval_translate]
  congr 2
  funext i
  fin_cases i <;> simp [coords]

lemma shift_ne_zero (p : PlanePoly) (hp : p ≠ 0) (d : GaussianInt) : shift d p ≠ 0 :=
  translate_ne_zero (coords d) hp

lemma coords_ne_zero (d : GaussianInt) (hd : d ≠ 0) : coords d 0 ≠ 0 ∨ coords d 1 ≠ 0 := by
  by_contra! he
  apply hd
  apply Zsqrtd.ext
  · exact_mod_cast (show (d.re : ℝ) = 0 from he.1)
  · exact_mod_cast (show (d.im : ℝ) = 0 from he.2)

lemma invariant_projection (p : PlanePoly) (hp : p ≠ 0) (d : GaussianInt)
    (hd : d ≠ 0) (h : shift d p = p) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∃ P : Polynomial ℝ, P ≠ 0 ∧
      ∀ z : GaussianInt, evalG p z = 0 → P.eval (a*(z.re : ℝ)+b*(z.im : ℝ)) = 0 := by
  let u := coords d 0
  let v := coords d 1
  have hperiod (z : Fin 2 → ℝ) (t : ℝ) := period_all_multiples p (coords d) h z t
  by_cases hu : u = 0
  · have hv : v ≠ 0 := (coords_ne_zero d hd).resolve_left (fun hnu => hnu hu)
    let P := lineRestriction p (fun _ => 0) ![1,0]
    have he (z : Fin 2 → ℝ) : P.eval (z 0) = eval z p := by
      have hh := hperiod z (-z 1/v)
      rw [eval_lineRestriction]
      convert hh using 2
      congr 1
      funext i
      fin_cases i
      · change 0+1*z 0 = z 0+u*(-z 1/v)
        rw [hu]; ring
      · change 0+0*z 0 = z 1+v*(-z 1/v)
        field_simp
        ring
    refine ⟨1,0,Or.inl one_ne_zero,P,?_,?_⟩
    · intro hP
      apply hp
      apply MvPolynomial.funext
      intro z
      rw [← he,hP,Polynomial.eval_zero,map_zero]
    · intro z hz
      simpa only [coords,Matrix.cons_val_zero,one_mul,zero_mul,add_zero] using
        (he (coords z)).trans hz
  · let P := lineRestriction p (fun _ => 0) ![0,1]
    have he (z : Fin 2 → ℝ) : P.eval (-(v/u)*z 0+z 1) = eval z p := by
      have hh := hperiod z (-z 0/u)
      rw [eval_lineRestriction]
      convert hh using 2
      congr 1
      funext i
      fin_cases i
      · change 0+0*(-(v/u)*z 0+z 1) = z 0+u*(-z 0/u)
        field_simp
        ring
      · change 0+1*(-(v/u)*z 0+z 1) = z 1+v*(-z 0/u)
        ring
    refine ⟨-(v/u),1,Or.inr one_ne_zero,P,?_,?_⟩
    · intro hP
      apply hp
      apply MvPolynomial.funext
      intro z
      rw [← he,hP,Polynomial.eval_zero,map_zero]
    · intro z hz
      simpa only [coords,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul] using
        (he (coords z)).trans hz

lemma invariant_line_cover (p : PlanePoly) (hp : p ≠ 0) (d : GaussianInt)
    (hd : d ≠ 0) (h : shift d p = p) :
    ∃ S : Finset Line, (∀ l ∈ S, l.Valid) ∧ ∀ z : GaussianInt,
      evalG p z = 0 → ∃ l ∈ S, l.eval z = 0 := by
  obtain ⟨a,b,hab,P,hP,he⟩ := invariant_projection p hp d hd h
  obtain ⟨S,hS,hcover⟩ := projection_line_cover a b hab P hP
  exact ⟨S,hS,fun z hz => hcover z (he z hz)⟩

#print axioms period_all_multiples
#print axioms invariant_line_cover
end
end Erdos952Investigation.MvPolynomialPeriod
