import FormalConjectures.AnalyticScratch
import FormalConjectures.PrimitiveLiftScratch

open Complex Finset
open scoped BigOperators
noncomputable section

namespace ImprimitivePos

lemma quadratic_eulerFactor_nonneg {f N : ℕ} [NeZero f] [NeZero N]
    (ψ : DirichletCharacter ℂ f) (hq : ψ.IsQuadratic) :
    0 ≤ (∏ p ∈ N.primeFactors, (1 - ψ p)).re ∧
      (∏ p ∈ N.primeFactors, (1 - ψ p)).im = 0 := by
  classical
  induction N.primeFactors using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [prod_insert hp]
      rcases hq p with h | h | h
      · rw [h]; simp_all
      · rw [h]; simp_all
      · rw [h]
        simp only [Complex.sub_re, one_re, neg_re, ofReal_neg, ofReal_one,
          Complex.sub_im, one_im, neg_im, sub_zero, Complex.mul_re, Complex.mul_im]
        constructor <;> nlinarith [ih.1]

lemma LFunction_zero_changeLevel_nonneg {f N : ℕ} [NeZero f] [NeZero N]
    (hf : f ∣ N) (ψ : DirichletCharacter ℂ f) (hq : ψ.IsQuadratic)
    (hpos : 0 ≤ (ψ.LFunction 0).re) :
    0 ≤ ((DirichletCharacter.changeLevel hf ψ).LFunction 0).re := by
  rw [DirichletCharacter.LFunction_changeLevel hf ψ (Or.inr (by norm_num))]
  simp only [neg_zero, cpow_zero, mul_one]
  have he := quadratic_eulerFactor_nonneg (N := N) ψ hq
  rw [Complex.mul_re, he.2, mul_zero, sub_zero]
  exact mul_nonneg hpos he.1

end ImprimitivePos
