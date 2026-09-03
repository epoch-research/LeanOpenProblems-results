import Submission.DiagonalQuadraticPolynomialRigidity

/-! All-degree polynomial rigidity for arbitrary positive definite rational
ternary quadratic forms. This is a construction obstruction only. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

private lemma positive_diagonalization (Q : QuadraticForm ℚ (Fin 3 → ℚ)) (hQ : Q.PosDef) :
    ∃ w : Fin 3 → ℚ, (∀ j, 0<w j) ∧
      Nonempty (Q.IsometryEquiv (QuadraticMap.weightedSumSquares ℚ w)) := by
  have hh : ∃ w : Fin 3 → ℚ, Q.Equivalent (QuadraticMap.weightedSumSquares ℚ w) := by
    have hh := Q.equivalent_weightedSumSquares
    have hd : Module.finrank ℚ (Fin 3 → ℚ)=3 := Module.finrank_fin_fun (R := ℚ) (n := 3)
    rw [hd] at hh
    exact hh
  obtain ⟨w,⟨L⟩⟩ := hh
  refine ⟨w,fun j ↦ ?_,⟨L⟩⟩
  let v : Fin 3 → ℚ := Pi.single j 1
  have hv : v ≠ 0 := by
    intro h
    have hh := congrFun h j
    simp [v] at hh
  have hp : L.symm v ≠ 0 := by
    intro h
    apply hv
    apply L.symm.injective
    simpa using h
  have hpos := hQ _ hp
  rw [L.symm.map_app] at hpos
  simpa [QuadraticMap.weightedSumSquares_apply,v,Pi.single_apply] using hpos

private def linearSubstitution (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ))
    (i : Fin 3) : MvPolynomial (Fin 3) ℚ :=
  ∑ j : Fin 3, MvPolynomial.C (L (Pi.single j 1) i)*MvPolynomial.X j

private lemma linearSubstitution_eval (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ))
    (x : Fin 3 → ℚ) (i : Fin 3) : MvPolynomial.eval x (linearSubstitution L i)=L x i := by
  have hx : (∑ j : Fin 3, x j • (Pi.single j (1 : ℚ) : Fin 3 → ℚ))=x := by
    funext k
    simp [Finset.sum_apply,Pi.single_apply]
  have hh := congrArg (fun v ↦ L v i) hx
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simpa [linearSubstitution,mul_comm] using hh

private lemma eval_substitution (L : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ))
    (P : MvPolynomial (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x (MvPolynomial.eval₂Hom MvPolynomial.C (linearSubstitution L) P)=
      MvPolynomial.eval (L x) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℚ) x
    (MvPolynomial.eval₂Hom MvPolynomial.C (linearSubstitution L) P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℚ) x).comp MvPolynomial.C=RingHom.id ℚ := by
    ext a
    simp
  rw [hc]
  change MvPolynomial.eval (fun i ↦ MvPolynomial.eval x (linearSubstitution L i)) P=_
  simp_rw [linearSubstitution_eval]

private lemma eval_rat_cast (P : MvPolynomial (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    realEval P (fun j ↦ (x j : ℝ))=(MvPolynomial.eval x P : ℝ) := by
  have he := MvPolynomial.map_eval₂Hom (RingHom.id ℚ) x (Rat.castHom ℝ) P
  rw [realEval,←MvPolynomial.eval₂_eq_eval_map]
  simpa only [RingHom.comp_id,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_id] using he.symm

/-- No polynomial family of any degree transfers multiplicity from a positive
rational ternary quadratic form to distinct quartic representations. -/
theorem positive_ternary_constant_on_rational_fibers
    (Q : QuadraticForm ℚ (Fin 3 → ℚ)) (hQ : Q.PosDef)
    (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H : Polynomial ℚ)
    (h : ∀ x : Fin 3 → ℚ, ∑ i, (MvPolynomial.eval x (P i))^4=H.eval (Q x))
    (x y : Fin 3 → ℚ) (hxy : Q x=Q y) (i : Fin 4) :
    MvPolynomial.eval x (P i)=MvPolynomial.eval y (P i) := by
  obtain ⟨w,hw,⟨L⟩⟩ := positive_diagonalization Q hQ
  let B : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) := L.symm.toLinearEquiv.toLinearMap
  let F (j : Fin 4) := MvPolynomial.eval₂Hom MvPolynomial.C (linearSubstitution B) (P j)
  have hF : ∑ j, F j^4=H.eval₂ MvPolynomial.C
      (∑ k : Fin 3, MvPolynomial.C (w k)*MvPolynomial.X k^2) := by
    apply MvPolynomial.funext
    intro u
    simp only [map_sum,map_pow]
    simp only [F,eval_substitution]
    rw [h]
    rw [Polynomial.hom_eval₂]
    have hc : (MvPolynomial.eval u).comp MvPolynomial.C=RingHom.id ℚ := by ext r; simp
    rw [hc]
    simp only [MvPolynomial.eval_C,MvPolynomial.eval_X,map_sum,map_mul,map_pow]
    change H.eval (Q (L.symm u))=H.eval (∑ k, w k*u k^2)
    rw [L.symm.map_app]
    simp [QuadraticMap.weightedSumSquares_apply,pow_two]
  have hnorm : ∑ j, (w j : ℝ)*((L x j : ℚ) : ℝ)^2=
      ∑ j, (w j : ℝ)*((L y j : ℚ) : ℝ)^2 := by
    have hh : (∑ j, w j*(L x j)^2)=(∑ j, w j*(L y j)^2) := by
      simpa only [QuadraticMap.weightedSumSquares_apply,smul_eq_mul,pow_two] using
        (L.map_app x).trans (hxy.trans (L.map_app y).symm)
    exact_mod_cast hh
  have hh := diagonal_constant_on_fibers w hw F H hF
    (fun j ↦ ((L x j : ℚ) : ℝ)) (fun j ↦ ((L y j : ℚ) : ℝ)) hnorm i
  rw [eval_rat_cast,eval_rat_cast] at hh
  have hh' : MvPolynomial.eval (L x) (F i)=MvPolynomial.eval (L y) (F i) := by exact_mod_cast hh
  simp only [F,eval_substitution] at hh'
  have hxL : B (L x)=x := L.toLinearEquiv.symm_apply_apply x
  have hyL : B (L y)=y := L.toLinearEquiv.symm_apply_apply y
  simpa only [hxL,hyL] using hh'


/-- A denominator depending only on the source quadratic value does not
restore distinct outputs on a fixed source fiber. -/
theorem positive_ternary_rational_fiber_unique
    (Q : QuadraticForm ℚ (Fin 3 → ℚ)) (hQ : Q.PosDef)
    (P : Fin 4 → MvPolynomial (Fin 3) ℚ) (H D : Polynomial ℚ)
    (h : ∀ x : Fin 3 → ℚ, ∑ i, (MvPolynomial.eval x (P i))^4=H.eval (Q x))
    (x y : Fin 3 → ℚ) (hxy : Q x=Q y) (i : Fin 4) :
    MvPolynomial.eval x (P i)/D.eval (Q x)=MvPolynomial.eval y (P i)/D.eval (Q y) := by
  rw [positive_ternary_constant_on_rational_fibers Q hQ P H h x y hxy i,hxy]

end
end Erdos322Research.QuadraticQuarticFive
