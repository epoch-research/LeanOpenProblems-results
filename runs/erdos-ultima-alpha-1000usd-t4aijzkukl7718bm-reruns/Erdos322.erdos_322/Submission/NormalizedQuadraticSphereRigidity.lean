import Submission.WeightedPlaneRotationRigidity
import Submission.EvenAxisQuarticRigidity

/-! All-degree rigidity for ternary quadratic sources with one good binary
subform. Rational polynomial coefficients are essential here. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

private abbrev const₂ : ℝ →+* Polynomial (Polynomial ℝ) :=
  (Polynomial.C : Polynomial ℝ →+* Polynomial (Polynomial ℝ)).comp Polynomial.C
private abbrev axisMap : MvPolynomial (Fin 3) ℚ →+* Polynomial (Polynomial ℝ) :=
  MvPolynomial.eval₂Hom (const₂.comp (Rat.castHom ℝ)) ![X,0,C X]

private lemma axis_eval (P : MvPolynomial (Fin 3) ℚ) (x z : ℝ) :
    (axisMap P).eval₂ (Polynomial.evalRingHom z) x=realEval P ![x,0,z] := by
  let E : Polynomial (Polynomial ℝ) →+* ℝ := Polynomial.eval₂RingHom (Polynomial.evalRingHom z) x
  change E (axisMap P)=_
  dsimp only [axisMap]
  rw [MvPolynomial.map_eval₂Hom]
  have hC : E.comp (const₂.comp (Rat.castHom ℝ))=Rat.castHom ℝ := by ext r; simp [E,const₂]
  have hX : (fun j : Fin 3 ↦ E (![X,0,C X] j))=![x,0,z] := by
    funext j
    fin_cases j <;> simp [E]
  rw [hC,hX]
  rw [realEval,←MvPolynomial.eval₂_eq_eval_map]
  rfl

private lemma bivariate_funext (f g : Polynomial (Polynomial ℝ))
    (h : ∀ x z : ℝ, f.eval₂ (Polynomial.evalRingHom z) x=g.eval₂ (Polynomial.evalRingHom z) x) :
    f=g := by
  apply Polynomial.ext
  intro n
  apply Polynomial.funext
  intro z
  have he : f.map (Polynomial.evalRingHom z)=g.map (Polynomial.evalRingHom z) := by
    apply Polynomial.funext
    intro x
    simpa only [eval_map] using h x z
  have hh := congrArg (fun p : Polynomial ℝ ↦ p.coeff n) he
  simpa only [coeff_map] using hh

/-- The entire real source fiber is constant, not only the selected rotation orbit. -/
theorem normalized_constant_on_fibers (d : ℤ) (hd : 0<d) (hg : GoodFive d)
    (e : ℚ) (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X))
    (x y : Fin 3 → ℝ) (hxy : sourceNorm (d : ℝ) (e : ℝ) x=sourceNorm (d : ℝ) (e : ℝ) y)
    (i : Fin 4) : realEval (P i) x=realEval (P i) y := by
  let f (j : Fin 4) := axisMap (P j)
  have hs (j : Fin 4) : (f j).comp (-X)=f j := by
    apply bivariate_funext
    intro a b
    rw [eval₂_comp]
    simp only [eval₂_neg,eval₂_X]
    change (axisMap (P j)).eval₂ (Polynomial.evalRingHom b) (-a)=
      (axisMap (P j)).eval₂ (Polynomial.evalRingHom b) a
    rw [axis_eval,axis_eval]
    have hh := real_rotation_invariant d hd hg e P H h ![a,0,b] (-1) 0 (by norm_num) j
    simpa [weightedRotate] using hh
  have hn : ∑ j, f j^4=(H.map (Rat.castHom ℝ)).eval₂ const₂
      (X^2+C (C (e : ℝ)*X^2)) := by
    have hh := congrArg axisMap h
    rw [Polynomial.hom_eval₂] at hh
    have hc : axisMap.comp MvPolynomial.C=const₂.comp (Rat.castHom ℝ) := by
      ext r
      simp [axisMap]
    have hx : axisMap (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X)=
        X^2+C (C (e : ℝ)*X^2) := by
      simp [sourceNorm,axisMap,const₂]
    simp only [map_sum,map_pow,hc,hx] at hh
    rw [Polynomial.eval₂_map]
    exact hh
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  let a := Real.sqrt (x 0^2+(d : ℝ)*x 1^2)
  let b := Real.sqrt (y 0^2+(d : ℝ)*y 1^2)
  have hab : a^2+(e : ℝ)*x 2^2=b^2+(e : ℝ)*y 2^2 := by
    have ha : a^2=x 0^2+(d : ℝ)*x 1^2 := Real.sq_sqrt (by positivity)
    have hb : b^2=y 0^2+(d : ℝ)*y 1^2 := Real.sq_sqrt (by positivity)
    rw [ha,hb]
    exact hxy
  have hh := bivariate_even_fiber (e : ℝ) f (H.map (Rat.castHom ℝ)) hs hn
    a (x 2) b (y 2) hab i
  change (axisMap (P i)).eval₂ (Polynomial.evalRingHom (x 2)) a=
    (axisMap (P i)).eval₂ (Polynomial.evalRingHom (y 2)) b at hh
  rw [axis_eval,axis_eval] at hh
  exact (axis_reduction d hd hg e P H h x i).symm.trans
    (hh.trans (axis_reduction d hd hg e P H h y i))

end
end Erdos322Research.QuadraticQuarticFive
