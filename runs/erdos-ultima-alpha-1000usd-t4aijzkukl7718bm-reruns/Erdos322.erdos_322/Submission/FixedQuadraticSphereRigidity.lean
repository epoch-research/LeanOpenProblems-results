import Submission.TernaryQuadraticLocalizationRigidity

/-! Rigidity on a single positive quadratic sphere. This is not a theorem
about unrestricted representation counts. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

private def stereoNum (d e : ℚ) : Fin 3 → TernaryPoly :=
  ![MvPolynomial.X 0^2-MvPolynomial.C d*MvPolynomial.X 1^2-
      MvPolynomial.C e*MvPolynomial.X 2^2,
    2*MvPolynomial.X 0*MvPolynomial.X 1,
    2*MvPolynomial.X 0*MvPolynomial.X 2]

private def stereoPoint (d e : ℚ) (j : Fin 3) : TernaryAway d e :=
  ternaryPolyMap d e (stereoNum d e j)*IsLocalization.Away.invSelf (ternaryDenom d e)

private lemma stereoPoint_norm (d e : ℚ) :
    sourceNorm (ternaryRatMap d e d) (ternaryRatMap d e e) (stereoPoint d e)=1 := by
  calc
    _ = (ternaryPolyMap d e (ternaryDenom d e)*
        IsLocalization.Away.invSelf (ternaryDenom d e))^2 := by
      simp only [sourceNorm,stereoPoint,stereoNum,ternaryDenom,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        map_sub,map_add,map_mul,map_pow,map_ofNat]
      change _=(((ternaryPolyMap d e (MvPolynomial.X 0))^2+
        ternaryRatMap d e d*(ternaryPolyMap d e (MvPolynomial.X 1))^2+
        ternaryRatMap d e e*(ternaryPolyMap d e (MvPolynomial.X 2))^2)*_)^2
      simp only [ternaryRatMap,RingHom.comp_apply,Matrix.head_cons,Matrix.tail_cons,
        map_mul,map_ofNat]
      ring
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf]; simp

private lemma at_inv (d e : ℚ) (x : Fin 3 → ℚ) (hx : sourceNorm d e x ≠ 0) :
    ternaryAt d e x hx (IsLocalization.Away.invSelf (ternaryDenom d e))=
      (sourceNorm d e x)⁻¹ := by
  have hh := congrArg (ternaryAt d e x hx)
    (IsLocalization.Away.mul_invSelf (ternaryDenom d e) (S := TernaryAway d e))
  simp only [map_mul,map_one,ternaryAt_poly,eval_ternaryDenom] at hh
  apply mul_left_cancel₀ hx
  rw [hh,mul_inv_cancel₀ hx]

private lemma stereoPoint_at (d e : ℚ) (x : Fin 3 → ℚ) (hx : sourceNorm d e x ≠ 0) :
    (fun j ↦ ternaryAt d e x hx (stereoPoint d e j))=
      ![(x 0^2-d*x 1^2-e*x 2^2)/sourceNorm d e x,
        (2*x 0*x 1)/sourceNorm d e x,(2*x 0*x 2)/sourceNorm d e x] := by
  funext j
  fin_cases j <;> simp [stereoPoint,stereoNum,at_inv,div_eq_mul_inv]

private lemma at_mv_eval (d e : ℚ) (x : Fin 3 → ℚ) (hx : sourceNorm d e x ≠ 0)
    (P : TernaryPoly) (u : Fin 3 → TernaryAway d e) :
    ternaryAt d e x hx (MvPolynomial.eval₂Hom (ternaryRatMap d e) u P)=
      MvPolynomial.eval (fun j ↦ ternaryAt d e x hx (u j)) P := by
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (ternaryAt d e x hx).comp (ternaryRatMap d e)=RingHom.id ℚ := by
    ext r
    simp
  rw [hc]
  rfl

private lemma stereoPoint_surjective (d e : ℚ) (hd : 0<d) (he : 0<e)
    (y : Fin 3 → ℚ) (hy : sourceNorm d e y=1) :
    ∃ (x : Fin 3 → ℚ) (hx : sourceNorm d e x ≠ 0),
      (fun j ↦ ternaryAt d e x hx (stereoPoint d e j))=y := by
  by_cases hy0 : y 0 = -1
  · have hh : d*y 1^2+e*y 2^2=0 := by simp [sourceNorm,hy0] at hy; linarith
    have hd0 : d ≠ 0 := ne_of_gt hd
    have he0 : e ≠ 0 := ne_of_gt he
    have hy1 : y 1=0 := by
      have hz : d*y 1^2=0 := le_antisymm (by nlinarith [mul_nonneg he.le (sq_nonneg (y 2))])
        (mul_nonneg hd.le (sq_nonneg (y 1)))
      exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hz).resolve_left hd0)
    have hy2 : y 2=0 := by
      have hz : e*y 2^2=0 := by simpa [hy1] using hh
      exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hz).resolve_left he0)
    have hx : sourceNorm d e (![0,1,0] : Fin 3 → ℚ) ≠ 0 := by
      simpa [sourceNorm] using hd0
    refine ⟨![0,1,0],hx,?_⟩
    rw [stereoPoint_at]
    funext j
    fin_cases j <;> simp [sourceNorm,hy0,hy1,hy2,hd0]
  · let x : Fin 3 → ℚ := ![1+y 0,y 1,y 2]
    have hs : (1 : ℚ)+y 0 ≠ 0 := by intro hz; apply hy0; linarith
    have hq : sourceNorm d e x=2*(1+y 0) := by
      dsimp [sourceNorm,x] at *
      nlinarith
    have hx : sourceNorm d e x ≠ 0 := by rw [hq]; exact mul_ne_zero (by norm_num) hs
    refine ⟨x,hx,?_⟩
    rw [stereoPoint_at,hq]
    funext j
    fin_cases j
    · change ((1+y 0)^2-d*y 1^2-e*y 2^2)/(2*(1+y 0))=y 0
      apply (div_eq_iff (mul_ne_zero (by norm_num) hs)).mpr
      dsimp [sourceNorm] at hy
      nlinarith
    · change (2*(1+y 0)*y 1)/(2*(1+y 0))=y 1
      field_simp
    · change (2*(1+y 0)*y 2)/(2*(1+y 0))=y 2
      field_simp

/-- Only one source level is assumed. Every polynomial map on that sphere
with constant four-coordinate fourth-power norm is constant there. -/
theorem fixed_diagonal_unit_sphere_constant (d e : ℚ) (hd : 0<d) (he : 0<e)
    (P : Fin 4 → TernaryPoly) (c : ℚ)
    (h : ∀ x : Fin 3 → ℚ, sourceNorm d e x=1 →
      ∑ i, (MvPolynomial.eval x (P i))^4=c) :
    ∃ b : Fin 4 → ℚ, ∀ x : Fin 3 → ℚ, sourceNorm d e x=1 →
      ∀ i, MvPolynomial.eval x (P i)=b i := by
  let f (i : Fin 4) : TernaryAway d e :=
    MvPolynomial.eval₂Hom (ternaryRatMap d e) (stereoPoint d e) (P i)
  have hf : ∑ i, f i^4=ternaryRatMap d e c := by
    apply ternaryAway_ext d e hd he
    intro x hx
    simp only [map_sum,map_pow,ternaryAt_rat,f,at_mv_eval]
    apply h
    have hh := congrArg (ternaryAt d e x hx) (stereoPoint_norm d e)
    simpa [sourceNorm] using hh
  obtain ⟨b,hb⟩ := ternary_localization_rigidity d e hd he f c hf
  refine ⟨b,fun y hy i ↦ ?_⟩
  obtain ⟨x,hx,heq⟩ := stereoPoint_surjective d e hd he y hy
  have hh := congrArg (ternaryAt d e x hx) (hb i)
  simp only [f,at_mv_eval,ternaryAt_rat,heq] at hh
  exact hh

end
end Erdos322Research.QuadraticQuarticFive
