import Submission.QuarticQuadraticMiddleZero

/-! Uniform zero counts for quadratic forms over F_5. These lemmas concern
polynomial constructions, not unrestricted quartic representation counts. -/
namespace Erdos322Research.QuarticQuadraticZeroSpectrum

open Finset MvPolynomial QuadraticMap
open QuarticQuadraticMiddleZero
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable instance : Invertible (2 : K) := invertibleOfNonzero (by decide)

def formZeroCount (Q : QuadraticForm K V) : ℕ :=
  (univ.filter (fun x : V => Q x = 0)).card

def diagonalZeroCount (w : V) : ℕ :=
  (univ.filter (fun x : V => ∑ i, w i*x i^2 = 0)).card

private def pairCount (a b t : K) : ℕ :=
  (univ.filter (fun p : K × K => a*p.1^2+b*p.2^2=t)).card

private def pairTable (a b t : K) : ℕ :=
  (![![![25, 0, 0, 0, 0], ![5, 10, 0, 0, 10], ![5, 0, 10, 10, 0], ![5, 0, 10, 10, 0], ![5, 10, 0, 0, 10]], ![![5, 10, 0, 0, 10], ![9, 4, 4, 4, 4], ![1, 6, 6, 6, 6], ![1, 6, 6, 6, 6], ![9, 4, 4, 4, 4]], ![![5, 0, 10, 10, 0], ![1, 6, 6, 6, 6], ![9, 4, 4, 4, 4], ![9, 4, 4, 4, 4], ![1, 6, 6, 6, 6]], ![![5, 0, 10, 10, 0], ![1, 6, 6, 6, 6], ![9, 4, 4, 4, 4], ![9, 4, 4, 4, 4], ![1, 6, 6, 6, 6]], ![![5, 10, 0, 0, 10], ![9, 4, 4, 4, 4], ![1, 6, 6, 6, 6], ![1, 6, 6, 6, 6], ![9, 4, 4, 4, 4]]] : Fin 5 → Fin 5 → Fin 5 → ℕ) a b t

private lemma pairCount_table : ∀ a b t : K, pairCount a b t = pairTable a b t := by
  decide +kernel

private def diagonalFormula (w : V) : ℕ :=
  ∑ t : K, pairTable (w 0) (w 1) t * pairTable (w 2) (w 3) (-t)

private def countEquiv (w : V) :
    {x : V // ∑ i, w i*x i^2=0} ≃
    Σ t : K, ({p : K × K // w 0*p.1^2+w 1*p.2^2=t} ×
      {p : K × K // w 2*p.1^2+w 3*p.2^2 = -t}) where
  toFun x := ⟨w 0*x.1 0^2+w 1*x.1 1^2,
    ⟨⟨(x.1 0,x.1 1),rfl⟩,⟨(x.1 2,x.1 3),by
      have h := x.2
      simp only [Fin.sum_univ_four] at h
      linear_combination h⟩⟩⟩
  invFun y := ⟨![y.2.1.1.1,y.2.1.1.2,y.2.2.1.1,y.2.2.1.2],by
    have ha := y.2.1.2
    have hb := y.2.2.2
    rw [Fin.sum_univ_four]
    change w 0*y.2.1.1.1^2 + w 1*y.2.1.1.2^2 +
      w 2*y.2.2.1.1^2 + w 3*y.2.2.1.2^2 = 0
    linear_combination ha+hb⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv y := by
    rcases y with ⟨t,⟨⟨⟨a,b⟩,ha⟩,⟨⟨c,d⟩,hb⟩⟩⟩
    dsimp at ha hb
    subst t
    rfl

private theorem diagonal_formula (w : V) : diagonalZeroCount w = diagonalFormula w := by
  have h := Fintype.card_congr (countEquiv w)
  simp only [Fintype.card_subtype, Fintype.card_sigma, Fintype.card_prod] at h
  change diagonalZeroCount w = ∑ t : K, pairCount (w 0) (w 1) t *
    pairCount (w 2) (w 3) (-t) at h
  simpa only [pairCount_table, diagonalFormula] using h

private lemma formula_bound : ∀ w : V, w ≠ 0 → diagonalFormula w ≤ 225 := by
  decide +kernel

private lemma formula_spectrum : ∀ w : V,
    diagonalFormula w = 25 ∨ diagonalFormula w = 105 ∨
    diagonalFormula w = 125 ∨ diagonalFormula w = 145 ∨
    diagonalFormula w = 225 ∨ diagonalFormula w = 625 := by
  decide +kernel

private lemma formula_maximal : ∀ w : V, diagonalFormula w = 225 →
    ∃ i j : Fin 4, ∃ r : K, i ≠ j ∧ w i ≠ 0 ∧ r ≠ 0 ∧
      w j = -w i*r^2 ∧ ∀ l, l ≠ i → l ≠ j → w l = 0 := by
  decide +kernel

private lemma diagonal_bound (w : V) (hw : w ≠ 0) : diagonalZeroCount w ≤ 225 := by
  rw [diagonal_formula]
  exact formula_bound w hw

private lemma diagonal_maximal (w : V) (hw : diagonalZeroCount w = 225) :
    ∃ i j : Fin 4, ∃ r : K, i ≠ j ∧ w i ≠ 0 ∧ r ≠ 0 ∧
      w j = -w i*r^2 ∧ ∀ l, l ≠ i → l ≠ j → w l = 0 := by
  exact formula_maximal w ((diagonal_formula w).symm.trans hw)

private theorem diagonalization (Q : QuadraticForm K V) :
    ∃ w : V, Nonempty (Q.IsometryEquiv (weightedSumSquares K w)) := by
  have h := QuadraticForm.equivalent_weightedSumSquares Q
  have hd : Module.finrank K V = 4 := by
    simpa only [Fintype.card_fin] using (Module.finrank_pi K (ι := Fin 4))
  rw [hd] at h
  exact h

private lemma zeroCount_isometry (Q : QuadraticForm K V) (w : V)
    (e : Q.IsometryEquiv (weightedSumSquares K w)) :
    formZeroCount Q = diagonalZeroCount w := by
  classical
  have he (x : V) : (∑ i, w i*(e x i)^2) = Q x := by
    simpa only [weightedSumSquares_apply, smul_eq_mul, pow_two] using e.map_app x
  let ee : {x : V // Q x = 0} ≃ {x : V // ∑ i, w i*x i^2 = 0} :=
    Equiv.subtypeEquiv e.toLinearEquiv.toEquiv (fun x => by
      change Q x = 0 ↔ (∑ i, w i*(e x i)^2) = 0
      rw [he x])
  have hh := Fintype.card_congr ee
  simpa only [Fintype.card_subtype, formZeroCount, diagonalZeroCount] using hh

/-- Every nonzero quadratic form over F_5 in four variables has at most 225
zeros, with no nondegeneracy assumption. -/
theorem form_zero_bound (Q : QuadraticForm K V) (hQ : Q ≠ 0) :
    formZeroCount Q ≤ 225 := by
  obtain ⟨w,⟨e⟩⟩ := diagonalization Q
  rw [zeroCount_isometry Q w e]
  apply diagonal_bound w
  intro hw
  apply hQ
  apply QuadraticMap.ext
  intro x
  have he := e.map_app x
  simpa [hw, weightedSumSquares_apply] using he.symm

/-- The complete zero-count spectrum, including the zero form. -/
theorem form_zero_spectrum (Q : QuadraticForm K V) :
    formZeroCount Q = 25 ∨ formZeroCount Q = 105 ∨
    formZeroCount Q = 125 ∨ formZeroCount Q = 145 ∨
    formZeroCount Q = 225 ∨ formZeroCount Q = 625 := by
  obtain ⟨w,⟨e⟩⟩ := diagonalization Q
  rw [zeroCount_isometry Q w e, diagonal_formula]
  exact formula_spectrum w

/-- Equality in the maximum zero count forces a factorization into two
linear forms. -/
theorem maximal_form_splits (Q : QuadraticForm K V)
    (hQ : formZeroCount Q = 225) :
    ∃ L M : V →ₗ[K] K, ∀ x, Q x = L x * M x := by
  obtain ⟨w,⟨e⟩⟩ := diagonalization Q
  rw [zeroCount_isometry Q w e] at hQ
  obtain ⟨i,j,r,hij,hwi,hr,hwj,hw⟩ := diagonal_maximal w hQ
  let A : V →ₗ[K] K := (LinearMap.proj i).comp e.toLinearEquiv.toLinearMap
  let B : V →ₗ[K] K := (LinearMap.proj j).comp e.toLinearEquiv.toLinearMap
  refine ⟨A+r • B, (w i) • (A-r • B), ?_⟩
  intro x
  have he : Q x = ∑ l, w l*(e x l)^2 := by
    simpa only [weightedSumSquares_apply, smul_eq_mul, pow_two] using (e.map_app x).symm
  rw [he, Finset.sum_eq_add_of_mem i j (mem_univ _) (mem_univ _) hij
    (fun l _ hl => by rw [hw l hl.1 hl.2, zero_mul]), hwj]
  change _ = (e x i + r*e x j)*(w i*(e x i-r*e x j))
  ring

end Erdos322Research.QuarticQuadraticZeroSpectrum
