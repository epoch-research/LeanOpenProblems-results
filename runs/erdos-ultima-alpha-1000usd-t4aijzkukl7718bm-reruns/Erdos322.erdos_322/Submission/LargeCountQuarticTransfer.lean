import Submission.LargeCountPolynomialDensity
import Submission.QuarticRationalSquareMultiplier

/-! High-count thresholds do not evade generic rational quartic-transfer
constraints. These results concern fixed formulas, not arbitrary exact counts. -/
namespace Erdos322Research.LargeCountQuarticTransfer
noncomputable section
open Finset LargeCountPolynomialDensity QuarticRationalSquareMultiplier
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- A rational norm-squaring formula valid above any fixed multiplicity
threshold extends to a generic polynomial identity after clearing denominators. -/
theorem square_identity_of_large_counts (M : ℕ) (C : ℚ)
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (D : MvPolynomial (Fin 4) ℚ)
    (hD : D ≠ 0)
    (h : ∀ a : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
      MvPolynomial.eval (fun i ↦ (a i : ℚ)) D ≠ 0 →
      (∑ i, (MvPolynomial.eval (fun j ↦ (a j : ℚ)) (P i) /
        MvPolynomial.eval (fun j ↦ (a j : ℚ)) D)^4) =
        C*((∑ i, a i^4 : ℕ) : ℚ)^2) :
    ∑ i, P i^4 = D^4*(MvPolynomial.C C*(∑ j : Fin 4, MvPolynomial.X j^4)^2) := by
  apply identity_of_large_counts_off_zero 2 M _ _ D hD
  intro a ha hd
  have hh := h a ha hd
  simp only [div_pow,← Finset.sum_div] at hh
  have he := (div_eq_iff (pow_ne_zero 4 hd)).mp hh
  simp only [map_sum,map_pow,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
    Nat.cast_sum,Nat.cast_pow] at he ⊢
  exact he.trans (mul_comm _ _)

/-- The same necessary two-adic multiplier shape holds even if a rational
formula is required only at targets with arbitrarily large multiplicity. -/
theorem high_count_multiplier_shape (M C : ℕ) (hC : 0 < C)
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (D : MvPolynomial (Fin 4) ℚ)
    (hD : D ≠ 0)
    (h : ∀ a : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
      MvPolynomial.eval (fun i ↦ (a i : ℚ)) D ≠ 0 →
      (∑ i, (MvPolynomial.eval (fun j ↦ (a j : ℚ)) (P i) /
        MvPolynomial.eval (fun j ↦ (a j : ℚ)) D)^4) =
        (C : ℚ)*((∑ i, a i^4 : ℕ) : ℚ)^2) :
    ∃ m u : ℕ, C=16^m*u ∧ u%64=4 :=
  rational_formula_multiplier_shape C hC P D hD
    (square_identity_of_large_counts M C P D hD h)

end
end Erdos322Research.LargeCountQuarticTransfer
