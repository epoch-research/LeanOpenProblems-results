import Submission.FixedPositiveQuadraticSphereRigidity

/-! Polynomial maps from finite products of fixed positive quadratic fibers
have no nonconstant constant-quartic-norm outputs. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0

private def blockSubstitution {ι : Type*} [DecidableEq ι] {n : ℕ}
    (x : ι → Fin n → ℚ) (j : ι) (k : ι × Fin n) : MvPolynomial (Fin n) ℚ :=
  if k.1=j then MvPolynomial.X k.2 else MvPolynomial.C (x k.1 k.2)

private lemma eval_blockSubstitution {ι : Type*} [DecidableEq ι] {n : ℕ}
    (x : ι → Fin n → ℚ) (j : ι) (P : MvPolynomial (ι × Fin n) ℚ) (z : Fin n → ℚ) :
    MvPolynomial.eval z (MvPolynomial.eval₂Hom MvPolynomial.C (blockSubstitution x j) P)=
      MvPolynomial.eval (Function.uncurry (Function.update x j z)) P := by
  change MvPolynomial.eval₂Hom (RingHom.id ℚ) z
    (MvPolynomial.eval₂Hom MvPolynomial.C (blockSubstitution x j) P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℚ) z).comp MvPolynomial.C=RingHom.id ℚ := by
    ext r
    simp
  rw [hc]
  change MvPolynomial.eval (fun k ↦ MvPolynomial.eval z (blockSubstitution x j k)) P=_
  apply congrArg (fun t ↦ MvPolynomial.eval t P)
  funext k
  by_cases hk : k.1=j <;> simp [blockSubstitution,Function.uncurry,hk]

/-- Holding all other blocks fixed, changing a block within its quadratic fiber
cannot change any output coordinate. -/
theorem fixed_quadratic_product_one_block {ι : Type*} [DecidableEq ι]
    (n : ℕ) (hn : 3≤n)
    (Q : ι → QuadraticForm ℚ (Fin n → ℚ)) (hQ : ∀ j, (Q j).PosDef)
    (P : Fin 4 → MvPolynomial (ι × Fin n) ℚ) (N : ι → ℚ) (c : ℚ)
    (h : ∀ x : ι → Fin n → ℚ, (∀ j, Q j (x j)=N j) →
      ∑ i, (MvPolynomial.eval (Function.uncurry x) (P i))^4=c)
    (x : ι → Fin n → ℚ) (hx : ∀ j, Q j (x j)=N j)
    (j : ι) (z : Fin n → ℚ) (hz : Q j z=N j) (i : Fin 4) :
    MvPolynomial.eval (Function.uncurry (Function.update x j z)) (P i)=
      MvPolynomial.eval (Function.uncurry x) (P i) := by
  let F (l : Fin 4) := MvPolynomial.eval₂Hom MvPolynomial.C (blockSubstitution x j) (P l)
  have hF (u : Fin n → ℚ) (hu : Q j u=N j) : ∑ l, (MvPolynomial.eval u (F l))^4=c := by
    simp only [F,eval_blockSubstitution]
    apply h
    intro k
    by_cases hk : k=j
    · subst k
      simpa using hu
    · simpa [Function.update_of_ne hk] using hx k
  have hh := fixed_positive_sphere_constant n hn (Q j) (hQ j) F (N j) c hF
    z (x j) hz (hx j) i
  simpa only [F,eval_blockSubstitution,Function.update_eq_self] using hh

/-- All source levels may be fixed independently. Polynomiality and the norm
identity force constancy on their entire finite product. -/
theorem fixed_quadratic_product_constant {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 3≤n)
    (Q : ι → QuadraticForm ℚ (Fin n → ℚ)) (hQ : ∀ j, (Q j).PosDef)
    (P : Fin 4 → MvPolynomial (ι × Fin n) ℚ) (N : ι → ℚ) (c : ℚ)
    (h : ∀ x : ι → Fin n → ℚ, (∀ j, Q j (x j)=N j) →
      ∑ i, (MvPolynomial.eval (Function.uncurry x) (P i))^4=c)
    (x y : ι → Fin n → ℚ) (hx : ∀ j, Q j (x j)=N j) (hy : ∀ j, Q j (y j)=N j)
    (i : Fin 4) : MvPolynomial.eval (Function.uncurry x) (P i)=
      MvPolynomial.eval (Function.uncurry y) (P i) := by
  classical
  let mix (s : Finset ι) (j : ι) := if j∈s then y j else x j
  have hm (s : Finset ι) (j : ι) : Q j (mix s j)=N j := by
    dsimp only [mix]
    split_ifs <;> [exact hy j; exact hx j]
  have hmix (s : Finset ι) : MvPolynomial.eval (Function.uncurry (mix s)) (P i)=
      MvPolynomial.eval (Function.uncurry x) (P i) := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert j s hj ih =>
      have heq : mix (insert j s)=Function.update (mix s) j (y j) := by
        funext k
        by_cases hk : k=j
        · subst k
          simp [mix]
        · simp [mix,hk]
      rw [heq]
      exact (fixed_quadratic_product_one_block n hn Q hQ P N c h (mix s) (hm s)
        j (y j) (hy j) i).trans ih
  have hh := hmix Finset.univ
  simpa [mix] using hh.symm

end
end Erdos322Research.QuadraticQuarticFive
