import Submission.QuadraticFactorCounting

/-! Joint distribution of a factor on distinct slopes, derived from lower-order
uniformity of every nontrivial factor character. This replaces a joint
character-discrepancy hypothesis by single-character uniformity hypotheses.
It does not assert those hypotheses for arbitrary local quadratic factors. -/
namespace Erdos3UniformFactorDistribution
open Finset Erdos3QuadraticFactorCounting Erdos3QuadraticModelTransfer
  Erdos3LinearFormsUniformity Erdos3FiniteUniformity Erdos3CorrelationSifting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {F G : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G]

lemma independent_characters_zero {I : Type*} [Fintype I] [DecidableEq I]
    (χ : I → AddChar G ℂ) (i : I) (hi : χ i ≠ 1) :
    (𝔼 y : I → G, ∏ j : I, χ j (y j)) = 0 := by
  have he : (𝔼 y : I → G, ∏ j : I, χ j (y j)) = ∏ j : I, 𝔼 y : G, χ j y := by
    simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
      Nat.cast_prod,prod_div_distrib]
  rw [he]
  apply prod_eq_zero (mem_univ i)
  exact AddChar.expect_eq_zero_iff_ne_zero.mpr hi

/-- Uniformity of every nontrivial factor character implies joint character
uniformity along distinct slopes. No polynomiality assumption is used. -/
theorem character_joint_discrepancy (n : ℕ) (v : Fin (n+2) → F)
    (hv : Function.Injective v) (q : F → G) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      uniformityPower n (fun x ↦ χ (q x)) ≤ ε^(2^(n+1)))
    (χ : Fin (n+2) → AddChar G ℂ) :
    ‖(𝔼 x : F, 𝔼 d : F, ∏ i : Fin (n+2), χ i (q (x+v i*d)))-
      (𝔼 y : Fin (n+2) → G, ∏ i : Fin (n+2), χ i (y i))‖ ≤ ε := by
  by_cases hall : ∀ i, χ i = 1
  · simp only [hall,AddChar.one_apply,prod_const_one,Fintype.expect_const,sub_self,norm_zero]
    exact hε
  · push_neg at hall
    obtain ⟨i,hi⟩ := hall
    rw [independent_characters_zero χ i hi,sub_zero]
    have h := distinct_slopes_bound n v hv (fun i x ↦ χ i (q x))
      (fun i x ↦ (χ i).norm_apply (q x) |>.le) i
    exact le_of_pow_le_pow_left₀ (by positivity : 2^(n+1) ≠ 0) hε
      (h.trans (hU (χ i) hi))

/-- Triple discrepancy, in the product-coordinate form used by the quadratic
model transfer theorem. -/
theorem triple_character_discrepancy (v : Fin 3 → F)
    (hv : Function.Injective v) (q : F → G) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      uniformityPower 1 (fun x ↦ χ (q x)) ≤ ε^4)
    (χ₀ χ₁ χ₂ : AddChar G ℂ) :
    ‖(𝔼 x : F, 𝔼 d : F,
        χ₀ (q (x+v 0*d))*χ₁ (q (x+v 1*d))*χ₂ (q (x+v 2*d)))-
      (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤ ε := by
  have h : ‖(𝔼 x : F, 𝔼 d : F, ∏ i : Fin 3, (![χ₀,χ₁,χ₂] i) (q (x+v i*d)))-
      (𝔼 y : Fin 3 → G, ∏ i : Fin 3, (![χ₀,χ₁,χ₂] i) (y i))‖ ≤ ε :=
    character_joint_discrepancy 1 v hv q hε (by simpa using hU) ![χ₀,χ₁,χ₂]
  have he : (𝔼 y : Fin 3 → G, ∏ i : Fin 3, (![χ₀,χ₁,χ₂] i) (y i)) =
      (𝔼 p : G × G × G, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2) := by
    have he : (𝔼 y : Fin 3 → G, ∏ i : Fin 3, (![χ₀,χ₁,χ₂] i) (y i)) =
        ∏ i : Fin 3, 𝔼 y : G, (![χ₀,χ₁,χ₂] i) y := by
      simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
        Nat.cast_prod,prod_div_distrib]
    rw [he]
    simp only [Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two]
    simp only [Erdos3QuadraticModelCounting.expect_triple,← expect_mul,← mul_expect]
    rfl
  rw [he] at h
  simpa only [Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two] using h

/-- Actual four-term configurations from a high-uniformity-order approximation
by a factor whose nontrivial characters are uniform at the lower order. -/
theorem exists_pattern_of_character_uniform_factor
    (v : Fin 4 → F) (hv : Function.Injective v)
    (A : Finset F) (q : F → G) (Φ : G → ℝ)
    (hΦ : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1)
    (hrel : ∀ x d : F,
      q (x+v 3*d) = q (x+v 0*d)-3 • q (x+v 1*d)+3 • q (x+v 2*d))
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hchar : ∀ χ : AddChar G ℂ, χ ≠ 1 →
      uniformityPower 1 (fun x ↦ χ (q x)) ≤ ε^4)
    (hU : uniformityPower 2 (fun x ↦ ((indicator A x-Φ (q x) : ℝ) : ℂ)) ≤ η^8)
    (hnum : ε*(Fintype.card G : ℝ)^2+4*η+density A/(Fintype.card F : ℝ) <
      (𝔼 y : G, Φ y)^4) :
    ∃ x d : F, d ≠ 0 ∧ ∀ i : Fin 4, x+v i*d ∈ A := by
  apply exists_pattern_of_quadratic_factor v hv A q Φ hΦ hrel hε hη ?_ hU hnum
  intro χ₀ χ₁ χ₂
  exact triple_character_discrepancy (fun i : Fin 3 ↦ v i.castSucc)
    (hv.comp (Fin.castSucc_injective 3)) q hε hchar χ₀ χ₁ χ₂

#print axioms character_joint_discrepancy
#print axioms exists_pattern_of_character_uniform_factor
end Erdos3UniformFactorDistribution
