import Submission.BinaryQuadraticGauss
import Submission.QuadraticModelTransfer

/-! Verifies the quadratic-model discrepancy hypothesis for sums of independent
squares over a finite field. The dimension supplies a power saving via exact
tensorization of the character averages. -/
namespace Erdos3QuadraticSquareDiscrepancy
open Finset Erdos3BinaryQuadraticGauss Erdos3QuadraticModelTransfer Erdos3QuadraticModelCounting
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {F : Type*} [Field F] [Fintype F]

lemma expect_pi_prod_complex {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → A → ℂ) :
    (𝔼 v : I → A, ∏ i, f i (v i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card,Fintype.card_pi,← Fintype.prod_sum,
    Nat.cast_prod,prod_div_distrib]

lemma independent_character_mean (χ₀ χ₁ χ₂ : AddChar F ℂ) :
    (𝔼 p : F × F × F, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2) =
      (𝔼 x : F, χ₀ x)*(𝔼 x : F, χ₁ x)*(𝔼 x : F, χ₂ x) := by
  rw [expect_triple]
  simp only [← mul_expect,← expect_mul]

lemma nonzero_quadratic_coefficients (h2 : (2 : F) ≠ 0) (a b c : F)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    a+b+c ≠ 0 ∨ 2*b+4*c ≠ 0 ∨ b+4*c ≠ 0 := by
  by_contra! hh
  have h4 : (4 : F) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1 <;> norm_num
  have hc : c = 0 := by
    apply (mul_eq_zero.mp (show (4 : F)*c = 0 by linear_combination 2*hh.2.2-hh.2.1)).resolve_left h4
  have hb : b = 0 := by simpa [hc] using hh.2.2
  have ha : a = 0 := by simpa [hb,hc] using hh.1
  tauto

lemma scalar_square_character_mean (χ : AddChar F ℂ) (a b c : F) :
    (𝔼 p : F × F, (χ.mulShift a) (p.1^2)*(χ.mulShift b) ((p.1+p.2)^2)*
      (χ.mulShift c) ((p.1+2*p.2)^2)) =
      binaryQuadraticMean χ (a+b+c) (2*b+4*c) (b+4*c) := by
  rw [show (𝔼 p : F × F, (χ.mulShift a) (p.1^2)*(χ.mulShift b) ((p.1+p.2)^2)*
      (χ.mulShift c) ((p.1+2*p.2)^2)) =
      𝔼 x : F, 𝔼 y : F, (χ.mulShift a) (x^2)*(χ.mulShift b) ((x+y)^2)*
        (χ.mulShift c) ((x+2*y)^2) from expect_product _ _ _]
  unfold binaryQuadraticMean
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  simp only [AddChar.mulShift_apply,← χ.map_add_eq_mul]
  congr 1
  ring

noncomputable def squareSample (n j : ℕ) (v : Fin n → F × F) : F :=
  ∑ i, ((v i).1+(j : F)*(v i).2)^2

lemma squareSample_relation (n : ℕ) (v : Fin n → F × F) :
    squareSample n 3 v = squareSample n 0 v-3 • squareSample n 1 v+3 • squareSample n 2 v := by
  simp only [squareSample,nsmul_eq_mul,mul_sum,sum_sub_distrib,← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  push_cast
  ring

lemma character_sum {I : Type*} (χ : AddChar F ℂ) (s : Finset I) (f : I → F) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,prod_empty,χ.map_zero_eq_one]
  | @insert a s ha ih => rw [sum_insert ha,prod_insert ha,χ.map_add_eq_mul,ih]

lemma squareSample_character_mean (n : ℕ) (χ₀ χ₁ χ₂ : AddChar F ℂ) :
    (𝔼 v : Fin n → F × F, χ₀ (squareSample n 0 v)*χ₁ (squareSample n 1 v)*
      χ₂ (squareSample n 2 v)) =
      (𝔼 p : F × F, χ₀ (p.1^2)*χ₁ ((p.1+p.2)^2)*χ₂ ((p.1+2*p.2)^2))^n := by
  simp only [squareSample,character_sum,Nat.cast_zero,zero_mul,add_zero,Nat.cast_one,one_mul,
    ← prod_mul_distrib]
  have h := expect_pi_prod_complex (fun (_ : Fin n) (p : F × F) ↦
      χ₀ (p.1^2)*χ₁ ((p.1+p.2)^2)*χ₂ ((p.1+2*p.2)^2))
  rw [prod_const,card_univ,Fintype.card_fin] at h
  simpa only [Nat.cast_ofNat] using h

/-- The character discrepancy of the first three square samples decays
geometrically in the independent dimension. -/
theorem squareSample_discrepancy (n : ℕ) (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) (χ₀ χ₁ χ₂ : AddChar F ℂ) :
    ‖(𝔼 v : Fin n → F × F, χ₀ (squareSample n 0 v)*χ₁ (squareSample n 1 v)*
        χ₂ (squareSample n 2 v))-
      (𝔼 p : F × F × F, χ₀ p.1*χ₁ p.2.1*χ₂ p.2.2)‖ ≤
      Real.sqrt (1/(Fintype.card F : ℝ))^n := by
  obtain ⟨a,rfl⟩ := primitive_characters_parameterized χ hχ χ₀
  obtain ⟨b,rfl⟩ := primitive_characters_parameterized χ hχ χ₁
  obtain ⟨c,rfl⟩ := primitive_characters_parameterized χ hχ χ₂
  by_cases h : a = 0 ∧ b = 0 ∧ c = 0
  · rcases h with ⟨rfl,rfl,rfl⟩
    simp only [AddChar.mulShift_zero,AddChar.one_apply,one_mul,Fintype.expect_const,sub_self,norm_zero]
    positivity
  · have hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by tauto
    have hind : (𝔼 p : F × F × F, (χ.mulShift a) p.1*(χ.mulShift b) p.2.1*(χ.mulShift c) p.2.2) = 0 := by
      rw [independent_character_mean]
      rcases hn with ha | hb | hc
      · rw [AddChar.expect_eq_zero_iff_ne_zero.mpr (hχ ha),zero_mul,zero_mul]
      · rw [AddChar.expect_eq_zero_iff_ne_zero.mpr (hχ hb),mul_zero,zero_mul]
      · rw [AddChar.expect_eq_zero_iff_ne_zero.mpr (hχ hc),mul_zero]
    rw [hind,sub_zero,squareSample_character_mean,scalar_square_character_mean,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (binaryQuadraticMean_norm_le χ hχ h2 _ _ _ (nonzero_quadratic_coefficients h2 a b c hn)) n

/-- Unconditional counting for every bounded function of a sum of independent
squares. This is a structured class, not the class of all subsets of naturals. -/
theorem squareSample_four_count (n : ℕ) (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) (f : F → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    (𝔼 y : F, f y)^4-Real.sqrt (1/(Fintype.card F : ℝ))^n*(Fintype.card F : ℝ)^2 ≤
      𝔼 v : Fin n → F × F,
        f (squareSample n 0 v)*f (squareSample n 1 v)*f (squareSample n 2 v)*f (squareSample n 3 v) := by
  exact quadratic_model_lower_bounded f hf (squareSample n 0) (squareSample n 1)
    (squareSample n 2) (squareSample n 3) (squareSample_relation n) (by positivity)
    (squareSample_discrepancy n χ hχ h2)

#print axioms scalar_square_character_mean
#print axioms squareSample_discrepancy
#print axioms squareSample_four_count
end Erdos3QuadraticSquareDiscrepancy
