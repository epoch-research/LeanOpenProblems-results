import Submission.QuadraticDenominatorRigidity

/-! A single rotationally invariant plane forces radiality of a polynomial
map to a real quartic sphere. The algebraic step is stated bivariately. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 0

lemma even_expand_contract {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (f : Polynomial R) (hf : f.comp (-X)=f) : expand R 2 (contract 2 f)=f := by
  ext n
  rw [coeff_expand (by decide : 0<2),coeff_contract (by decide : 2 ≠ 0)]
  by_cases hn : 2 ∣ n
  · simp [hn,Nat.div_mul_cancel hn]
  · simp only [hn,if_false]
    have hodd : Odd n := by rw [Nat.odd_iff]; omega
    have hh := congrArg (fun p : Polynomial R ↦ p.coeff n) hf
    dsimp only at hh
    rw [show (-X : Polynomial R)=C (-1)*X by simp,comp_C_mul_X_coeff,hodd.neg_one_pow] at hh
    have h2 : (2 : R)*f.coeff n=0 := by linear_combination -hh
    exact ((mul_eq_zero.mp h2).resolve_left (by exact_mod_cast (by decide : (2 : ℕ) ≠ 0))).symm

private abbrev const₂ : ℝ →+* Polynomial (Polynomial ℝ) :=
  (Polynomial.C : Polynomial ℝ →+* Polynomial (Polynomial ℝ)).comp Polynomial.C

/-- If the axis restriction is even in its first variable, its output only
depends on the value of the source quadratic form, at every degree. -/
theorem bivariate_even_fiber (e : ℝ) (f : Fin 4 → Polynomial (Polynomial ℝ))
    (H : Polynomial ℝ) (hs : ∀ i, (f i).comp (-X)=f i)
    (hn : ∑ i, f i^4=H.eval₂ const₂ (X^2+C (C e*X^2)))
    (x z y w : ℝ) (hxy : x^2+e*z^2=y^2+e*w^2) (i : Fin 4) :
    (f i).eval₂ (Polynomial.evalRingHom z) x=
      (f i).eval₂ (Polynomial.evalRingHom w) y := by
  let g (j : Fin 4) := contract 2 (f j)
  have hg (j : Fin 4) : expand (Polynomial ℝ) 2 (g j)=f j := even_expand_contract (f j) (hs j)
  have hE : (expand (Polynomial ℝ) 2).toRingHom.comp const₂=const₂ := by
    ext r
    simp [const₂]
  have hgn : ∑ j, g j^4=H.eval₂ const₂ (X+C (C e*X^2)) := by
    apply expand_injective (by decide : 0<2)
    have hex : expand (Polynomial ℝ) 2 (H.eval₂ const₂ (X+C (C e*X^2)))=
        H.eval₂ const₂ (X^2+C (C e*X^2)) := by
      change (expand (Polynomial ℝ) 2).toRingHom _=_
      rw [Polynomial.hom_eval₂,hE]
      simp
    simpa only [map_sum,map_pow,hg,hex] using hn
  let n := x^2+e*z^2
  let E : Polynomial (Polynomial ℝ) →+* Polynomial ℝ :=
    Polynomial.eval₂RingHom (RingHom.id (Polynomial ℝ)) (C n-C e*X^2)
  have hEC : E.comp const₂=Polynomial.C := by ext r; simp [E,const₂]
  have harg : E (X+C (C e*X^2))=C n := by simp [E]
  have hnorm : ∑ j, (E (g j))^4=C (H.eval n) := by
    have hh := congrArg E hgn
    simp only [map_sum,map_pow,Polynomial.hom_eval₂,hEC,harg] at hh
    simpa only [Polynomial.eval₂_at_apply] using hh
  have hc := constant_coordinates (fun j ↦ E (g j)) (H.eval n) hnorm
  dsimp only at hc
  have hp (a b : ℝ) (hab : a^2+e*b^2=n) :
      (f i).eval₂ (Polynomial.evalRingHom b) a=(E (g i)).coeff 0 := by
    have hbase : n-e*b^2=a^2 := by linarith
    have heval : (E (g i)).eval b=(g i).eval₂ (Polynomial.evalRingHom b) (a^2) := by
      change Polynomial.evalRingHom b (Polynomial.eval₂ (RingHom.id (Polynomial ℝ))
        (C n-C e*X^2) (g i))=_
      rw [Polynomial.hom_eval₂]
      simp [hbase]
    rw [←hg i,expand_eq_comp_X_pow,eval₂_comp]
    simp only [eval₂_pow,eval₂_X]
    rw [←heval,hc i,eval_C,coeff_C_zero]
  exact (hp x z rfl).trans (hp y w hxy.symm).symm

end
end Erdos322Research.QuadraticQuarticFive
