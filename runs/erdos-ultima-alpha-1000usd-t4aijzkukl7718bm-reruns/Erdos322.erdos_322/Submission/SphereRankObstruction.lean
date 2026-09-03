import FormalConjecturesUtil

/-! A rank obstruction to linear constructions from ternary quadratic norms. -/
namespace Erdos322Research.SphereRank

private def testPoints : Fin 15 → Fin 3 → ℝ :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![1, 1, 0],
    ![1, -1, 0],
    ![2, 1, 0],
    ![1, 0, 1],
    ![1, 0, -1],
    ![2, 0, 1],
    ![0, 1, 1],
    ![0, 1, -1],
    ![0, 2, 1],
    ![1, 1, 1],
    ![1, 1, -1],
    ![1, -1, 1]]

private def weights (q : Fin 6 → ℝ) : Fin 15 → ℝ :=
  ![12*q 0^2 - 4*q 0*q 1 - 4*q 0*q 2 - 12*q 0*q 3 - 12*q 0*q 4 - 2*q 0*q 5 + 12*q 1*q 3 + 2*q 1*q 4 + 2*q 2*q 3 + 12*q 2*q 4 - 2*q 3^2 - 2*q 3*q 4 + 2*q 3*q 5 - 2*q 4^2 + 2*q 4*q 5,
    -4*q 0*q 1 + 3*q 0*q 3 - 2*q 0*q 5 + 12*q 1^2 - 4*q 1*q 2 - 3*q 1*q 3 + 2*q 1*q 4 - 12*q 1*q 5 + 2*q 2*q 3 + 12*q 2*q 5 - 2*q 3^2 - 2*q 3*q 4 + 2*q 3*q 5 + 2*q 4*q 5 - 2*q 5^2,
    -4*q 0*q 2 + 3*q 0*q 4 - 2*q 0*q 5 - 4*q 1*q 2 + 2*q 1*q 4 + 3*q 1*q 5 + 12*q 2^2 + 2*q 2*q 3 - 3*q 2*q 4 - 3*q 2*q 5 - 2*q 3*q 4 + 2*q 3*q 5 - 2*q 4^2 + 2*q 4*q 5 - 2*q 5^2,
    2*q 0*q 1 - 3*q 0*q 3 + q 0*q 5 + 6*q 1*q 3 - q 1*q 4 - 2*q 2*q 3 + q 3^2 + q 3*q 4 - q 3*q 5 - 2*q 4*q 5,
    2*q 0*q 1 - q 0*q 3 + q 0*q 5 - 2*q 1*q 3 - q 1*q 4 + q 3^2 + q 3*q 4 - q 3*q 5,
    q 0*q 3 - q 1*q 3,
    2*q 0*q 2 - 3*q 0*q 4 + q 0*q 5 - 2*q 1*q 4 - q 2*q 3 + 6*q 2*q 4 + q 3*q 4 - 2*q 3*q 5 + q 4^2 - q 4*q 5,
    2*q 0*q 2 - q 0*q 4 + q 0*q 5 - q 2*q 3 - 2*q 2*q 4 + q 3*q 4 + q 4^2 - q 4*q 5,
    q 0*q 4 - q 2*q 4,
    2*q 1*q 2 - q 1*q 4 - 3*q 1*q 5 - q 2*q 3 + 6*q 2*q 5 - q 3*q 5 - q 4*q 5 + q 5^2,
    2*q 0*q 5 + 2*q 1*q 2 - q 1*q 4 - q 1*q 5 - q 2*q 3 - 2*q 2*q 5 + 2*q 3*q 4 - q 3*q 5 - q 4*q 5 + q 5^2,
    q 1*q 5 - q 2*q 5,
    q 1*q 4 + q 2*q 3 + q 3*q 5 + q 4*q 5,
    -q 0*q 5 + q 2*q 3 - q 3*q 4 + q 4*q 5,
    -q 0*q 5 + q 1*q 4 - q 3*q 4 + q 3*q 5]

private def quadraticEval (a : Fin 3 → ℝ) (q : Fin 6 → ℝ) : ℝ :=
  q 0*a 0^2 + q 1*a 1^2 + q 2*a 2^2 + q 3*a 0*a 1 + q 4*a 0*a 2 + q 5*a 1*a 2

private def positiveForm (q : Fin 6 → ℝ) : ℝ :=
  2*((q 0)^2+(q 1)^2+(q 2)^2)+(q 0+q 1+q 2)^2+(q 3)^2+(q 4)^2+(q 5)^2

private theorem quartic_polarization (a : Fin 3 → ℝ) (q : Fin 6 → ℝ) :
    12 * quadraticEval a q ^ 2 =
      ∑ j, weights q j * (∑ k, a k * testPoints j k)^4 := by
  norm_num [quadraticEval, weights, testPoints, Fin.sum_univ_succ]
  ring

private theorem weights_norm (q : Fin 6 → ℝ) :
    ∑ j, weights q j * (∑ k, testPoints j k ^ 2)^2 = 4 * positiveForm q := by
  norm_num [positiveForm, weights, testPoints, Fin.sum_univ_succ]
  ring

private theorem gram_identity {ι : Type*} [Fintype ι] (a : ι → Fin 3 → ℝ)
    (C : ℝ) (h : ∀ x : Fin 3 → ℝ,
      ∑ i, (∑ j, a i j * x j)^4 = C * (∑ j, x j^2)^2) (q : Fin 6 → ℝ) :
    12 * (∑ i, quadraticEval (a i) q ^ 2) = 4*C*positiveForm q := by
  calc
    12 * (∑ i, quadraticEval (a i) q ^ 2) =
        ∑ i, ∑ j, weights q j * (∑ k, a i k * testPoints j k)^4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact quartic_polarization (a i) q
    _ = ∑ j, weights q j * (∑ i, (∑ k, a i k * testPoints j k)^4) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ j, weights q j * (C * (∑ k, testPoints j k ^ 2)^2) := by simp_rw [h]
    _ = C * (∑ j, weights q j * (∑ k, testPoints j k ^ 2)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 4*C*positiveForm q := by rw [weights_norm]; ring

private theorem positiveForm_eq_zero {q : Fin 6 → ℝ} (h : positiveForm q = 0) : q = 0 := by
  have h₀ := sq_nonneg (q 0)
  have h₁ := sq_nonneg (q 1)
  have h₂ := sq_nonneg (q 2)
  have h₃ := sq_nonneg (q 3)
  have h₄ := sq_nonneg (q 4)
  have h₅ := sq_nonneg (q 5)
  have hs := sq_nonneg (q 0+q 1+q 2)
  dsimp [positiveForm] at h
  funext i
  fin_cases i
  · change q 0 = 0
    nlinarith
  · change q 1 = 0
    nlinarith
  · change q 2 = 0
    nlinarith
  · change q 3 = 0
    nlinarith
  · change q 4 = 0
    nlinarith
  · change q 5 = 0
    nlinarith

/-- At least six real linear forms are required for their fourth powers to sum
exactly to a positive multiple of the square of a ternary Euclidean norm. -/
theorem at_least_six_forms {ι : Type*} [Fintype ι] (a : ι → Fin 3 → ℝ)
    (C : ℝ) (hC : 0 < C) (h : ∀ x : Fin 3 → ℝ,
      ∑ i, (∑ j, a i j * x j)^4 = C * (∑ j, x j^2)^2) :
    6 ≤ Fintype.card ι := by
  let L : (Fin 6 → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun q i ↦ quadraticEval (a i) q
      map_add' := by
        intro q r
        funext i
        simp only [quadraticEval, Pi.add_apply]
        ring
      map_smul' := by
        intro c q
        funext i
        simp only [quadraticEval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hL : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro q hq
    apply positiveForm_eq_zero
    have he := gram_identity a C h q
    have hz : ∀ i, quadraticEval (a i) q = 0 := fun i ↦ congrFun hq i
    simp_rw [hz] at he
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (by positivity)
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  simpa using hdim

/-- In particular, no linear ternary norm construction can produce the desired
four-coordinate quartic representations. -/
theorem no_four_form_identity : ¬ ∃ (a : Fin 4 → Fin 3 → ℝ) (C : ℝ), 0 < C ∧
    ∀ x : Fin 3 → ℝ, ∑ i, (∑ j, a i j * x j)^4 = C * (∑ j, x j^2)^2 := by
  rintro ⟨a, C, hC, h⟩
  have := at_least_six_forms a C hC h
  norm_num at this

end Erdos322Research.SphereRank
