import Submission.LargeCountPolynomialDensity

/-! Cartesian products of two sets of large-count tuples are Zariski dense.
This extends fixed-identity testing to two independently varying targets. -/
namespace Erdos322Research.LargeCountPairDensity

open LargeCountPolynomialDensity
set_option Elab.async false

private noncomputable def leftSub (a : Fin 4 → ℚ) :
    MvPolynomial (Fin 4 ⊕ Fin 4) ℚ →+* MvPolynomial (Fin 4) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i ↦ MvPolynomial.C (a i)) MvPolynomial.X)

private noncomputable def rightSub (b : Fin 4 → ℚ) :
    MvPolynomial (Fin 4 ⊕ Fin 4) ℚ →+* MvPolynomial (Fin 4) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun i ↦ MvPolynomial.C (b i)))

private lemma eval_leftSub (a b : Fin 4 → ℚ) (P : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) :
    MvPolynomial.eval b (leftSub a P) = MvPolynomial.eval (Sum.elim a b) P := by
  have he : (MvPolynomial.eval b).comp (leftSub a) = MvPolynomial.eval (Sum.elim a b) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [leftSub]
    · intro i
      cases i <;> simp [leftSub]
  exact congrArg (fun f : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ →+* ℚ ↦ f P) he

private lemma eval_rightSub (a b : Fin 4 → ℚ) (P : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) :
    MvPolynomial.eval a (rightSub b P) = MvPolynomial.eval (Sum.elim a b) P := by
  have he : (MvPolynomial.eval a).comp (rightSub b) = MvPolynomial.eval (Sum.elim a b) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rightSub]
    · intro i
      cases i <;> simp [rightSub]
  exact congrArg (fun f : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ →+* ℚ ↦ f P) he

/-- The two targets need not coincide. A polynomial vanishing whenever both
counts exceed their prescribed thresholds must vanish identically. -/
theorem eq_zero_of_vanish_on_large_pair_counts (M N : ℕ)
    (P : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (h : ∀ a b : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
      N < Erdos322.representationCount 4 (∑ i, b i^4) →
      MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) P = 0) : P=0 := by
  have hl (a : Fin 4 → ℕ) (ha : M < Erdos322.representationCount 4 (∑ i, a i^4)) :
      leftSub (fun i ↦ (a i : ℚ)) P=0 := by
    apply eq_zero_of_vanish_on_large_counts 2 N
    intro b hb
    rw [eval_leftSub]
    exact h a b ha hb
  have hr (b : Fin 4 → ℚ) : rightSub b P=0 := by
    apply eq_zero_of_vanish_on_large_counts 2 M
    intro a ha
    rw [eval_rightSub]
    have hh := congrArg (MvPolynomial.eval b) (hl a ha)
    simpa only [eval_leftSub,map_zero] using hh
  apply MvPolynomial.funext
  intro x
  have hh := congrArg (MvPolynomial.eval (fun i ↦ x (Sum.inl i))) (hr (fun i ↦ x (Sum.inr i)))
  have hx : Sum.elim (fun i ↦ x (Sum.inl i)) (fun i ↦ x (Sum.inr i)) = x := by
    funext i
    cases i <;> rfl
  simpa only [eval_rightSub,map_zero,hx] using hh

/-- A fixed exceptional polynomial denominator may be excluded without
weakening the resulting generic identity. -/
theorem identity_of_large_pair_counts_off_zero (M N : ℕ)
    (P Q D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0)
    (h : ∀ a b : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
      N < Erdos322.representationCount 4 (∑ i, b i^4) →
      MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) D ≠ 0 →
      MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) P =
      MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) Q) : P=Q := by
  have hz : D*(P-Q)=0 := by
    apply eq_zero_of_vanish_on_large_pair_counts M N
    intro a b ha hb
    rw [map_mul,map_sub]
    by_cases hd : MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) D=0
    · rw [hd,zero_mul]
    · rw [h a b ha hb hd,sub_self,mul_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hD)

end Erdos322Research.LargeCountPairDensity
