import Submission.LargeCountPairDensity
import Submission.QuarticScaledRationalProduct

/-! Multiplicity thresholds do not permit a fixed scaled rational product
formula for quartic norms. No restriction on formula degree or coordinate-
dependent denominators is imposed. This does not bound unrestricted counts. -/
namespace Erdos322Research.LargeCountScaledProduct

open Finset LargeCountPairDensity QuarticScaledRationalProduct
set_option Elab.async false

/-- A rational formula that multiplies all pairs of sufficiently high-count
quartic targets already gives a generic polynomial identity. -/
theorem product_identity_of_large_counts (M N : ℕ) (C : ℚ)
    (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0)
    (h : ∀ a b : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
      N < Erdos322.representationCount 4 (∑ i, b i^4) →
      MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) D ≠ 0 →
      ∑ i, (MvPolynomial.eval (Sum.elim (fun j ↦ (a j : ℚ)) (fun j ↦ (b j : ℚ))) (P i) /
        MvPolynomial.eval (Sum.elim (fun j ↦ (a j : ℚ)) (fun j ↦ (b j : ℚ))) D)^4 =
        C*(∑ i, (a i : ℚ)^4)*(∑ i, (b i : ℚ)^4)) :
    ∑ i, P i^4 = D^4*(MvPolynomial.C C*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inl i)^4)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inr i)^4)) := by
  apply identity_of_large_pair_counts_off_zero M N _ _ D hD
  intro a b ha hb hd
  have hh := h a b ha hb hd
  simp only [div_pow,← Finset.sum_div] at hh
  have he := (div_eq_iff (pow_ne_zero 4 hd)).mp hh
  simpa only [map_sum,map_pow,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
    Sum.elim_inl,Sum.elim_inr,mul_comm] using he

/-- No fixed positive rational multiplier works in such a rational formula,
even after imposing any two fixed multiplicity thresholds. The two input
targets vary independently; equal-target-only constructions are not excluded. -/
theorem no_high_count_scaled_product (M N : ℕ) (C : ℚ) (hC : 0 < C)
    (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0) :
    ¬ (∀ a b : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
      N < Erdos322.representationCount 4 (∑ i, b i^4) →
      MvPolynomial.eval (Sum.elim (fun i ↦ (a i : ℚ)) (fun i ↦ (b i : ℚ))) D ≠ 0 →
      ∑ i, (MvPolynomial.eval (Sum.elim (fun j ↦ (a j : ℚ)) (fun j ↦ (b j : ℚ))) (P i) /
        MvPolynomial.eval (Sum.elim (fun j ↦ (a j : ℚ)) (fun j ↦ (b j : ℚ))) D)^4 =
        C*(∑ i, (a i : ℚ)^4)*(∑ i, (b i : ℚ)^4)) := by
  intro h
  exact no_positive_rational_product_scale C hC P D hD
    (product_identity_of_large_counts M N C P D hD h)

end Erdos322Research.LargeCountScaledProduct
