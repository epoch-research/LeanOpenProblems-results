import Submission.NormalizedQuadraticSphereRigidity
import Submission.QuadraticGoodPair

/-! Every rational polynomial map from a positive rational ternary quadratic
source to a four-coordinate quartic sphere is constant on source fibers,
without a degree or homogeneity restriction. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private lemma permutation_pair (i j : Fin 3) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0=i ∧ σ 1=j := by
  have hh : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0=i ∧ σ 1=j := by decide
  exact hh i j hij

/-- All-degree rigidity for arbitrary positive rational diagonal ternary forms. -/
theorem diagonal_constant_on_fibers (a : Fin 3 → ℚ) (ha : ∀ j, 0<a j)
    (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∑ i, P i^4=H.eval₂ MvPolynomial.C
      (∑ j : Fin 3, MvPolynomial.C (a j)*MvPolynomial.X j^2))
    (x y : Fin 3 → ℝ) (hxy : ∑ j, (a j : ℝ)*x j^2=∑ j, (a j : ℝ)*y j^2)
    (l : Fin 4) : realEval (P l) x=realEval (P l) y := by
  obtain ⟨i,j,hij,d,hd,hgood,t,ht,hij'⟩ := exists_good_rational_pair a ha
  obtain ⟨σ,hσ0,hσ1⟩ := permutation_pair i j hij
  let e : ℚ := a (σ 2)/a i
  let z : Fin 3 → MvPolynomial (Fin 3) ℚ := fun k ↦
    ![MvPolynomial.X 0,MvPolynomial.C (t⁻¹)*MvPolynomial.X 1,MvPolynomial.X 2] (σ.symm k)
  let T : MvPolynomial (Fin 3) ℚ →+* MvPolynomial (Fin 3) ℚ :=
    MvPolynomial.eval₂Hom MvPolynomial.C z
  let Q : Fin 4 → MvPolynomial (Fin 3) ℚ := fun k ↦ T (P k)
  let H' := H.comp (C (a i)*X)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hai : a i ≠ 0 := ne_of_gt (ha i)
  have hcoef1 : a j*(t⁻¹)^2=a i*(d : ℚ) := by rw [hij']; field_simp
  have hcoef2 : a i*e=a (σ 2) := by dsimp [e]; field_simp
  have hs : T (∑ k : Fin 3, MvPolynomial.C (a k)*MvPolynomial.X k^2)=
      MvPolynomial.C (a i)*sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X := by
    simp only [T,map_sum,map_mul,map_pow,MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X']
    rw [←Equiv.sum_comp σ (fun k ↦ MvPolynomial.C (a k)*z k^2)]
    simp only [Fin.sum_univ_three,z,Equiv.symm_apply_apply,hσ0,hσ1,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,sourceNorm]
    have hc1 : MvPolynomial.C (σ := Fin 3) (a j)*(MvPolynomial.C (t⁻¹))^2=
        MvPolynomial.C (a i)*MvPolynomial.C (d : ℚ) := by
      rw [←map_pow,←map_mul,←map_mul,hcoef1]
    have hc2 : MvPolynomial.C (σ := Fin 3) (a i)*MvPolynomial.C e=MvPolynomial.C (a (σ 2)) := by
      rw [←map_mul,hcoef2]
    linear_combination (MvPolynomial.X (1 : Fin 3))^2*hc1-(MvPolynomial.X (2 : Fin 3))^2*hc2
  have hQ : ∑ k, Q k^4=H'.eval₂ MvPolynomial.C
      (sourceNorm (MvPolynomial.C (d : ℚ)) (MvPolynomial.C e) MvPolynomial.X) := by
    have hh := congrArg T h
    rw [Polynomial.hom_eval₂] at hh
    have hTC : T.comp MvPolynomial.C=MvPolynomial.C := by ext r; simp [T]
    simp only [map_sum,map_pow,hTC,hs] at hh
    dsimp only [H']
    rw [eval₂_comp]
    simpa only [eval₂_mul,eval₂_C,eval₂_X] using hh
  let u (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![v (σ 0),(t : ℝ)*v (σ 1),v (σ 2)]
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
  have hz (v : Fin 3 → ℝ) (k : Fin 3) :
      MvPolynomial.eval₂Hom (Rat.castHom ℝ) (u v) (z k)=v k := by
    obtain ⟨k,rfl⟩ := σ.surjective k
    fin_cases k <;> simp [z,u,htR]
  have hEval (v : Fin 3 → ℝ) (k : Fin 4) : realEval (Q k) (u v)=realEval (P k) v := by
    simp only [realEval,←MvPolynomial.eval₂_eq_eval_map]
    change MvPolynomial.eval₂Hom (Rat.castHom ℝ) (u v) (T (P k))=_
    dsimp only [T]
    rw [MvPolynomial.map_eval₂Hom]
    have hc : (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (u v)).comp MvPolynomial.C=Rat.castHom ℝ := by
      ext r
      simp
    rw [hc]
    simp_rw [hz v]
    rfl
  have hscale (v : Fin 3 → ℝ) : (∑ k, (a k : ℝ)*v k^2)=
      (a i : ℝ)*sourceNorm (d : ℝ) (e : ℝ) (u v) := by
    have hh := congrArg (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (u v)) hs
    dsimp only [T] at hh
    rw [MvPolynomial.map_eval₂Hom] at hh
    have hc : (MvPolynomial.eval₂Hom (Rat.castHom ℝ) (u v)).comp MvPolynomial.C=Rat.castHom ℝ := by
      ext r
      simp
    rw [hc] at hh
    simp_rw [hz v] at hh
    simpa [sourceNorm] using hh
  have hu : sourceNorm (d : ℝ) (e : ℝ) (u x)=sourceNorm (d : ℝ) (e : ℝ) (u y) := by
    apply mul_left_cancel₀ (show (a i : ℝ) ≠ 0 by exact_mod_cast hai)
    exact (hscale x).symm.trans (hxy.trans (hscale y))
  have hdZ : (0 : ℤ)<d := by exact_mod_cast hd
  have hh := normalized_constant_on_fibers (d : ℤ) hdZ hgood e Q H' hQ (u x) (u y) hu l
  rw [hEval,hEval] at hh
  exact hh

end
end Erdos322Research.QuadraticQuarticFive
