import Submission.PrimeDilutionGeneral

/-! A necessary cardinality budget for large-modulus thinning. This limits a
proposed way to combine existing void estimates with soft Laplace cylinders;
it is not a disproof of Erdős 970. -/
namespace Erdos970.PrimeDilution
open Finset Real
set_option maxHeartbeats 1000000

lemma neg_log_one_sub_inv_le (p : ℝ) (hp : 1 < p) :
    -log (1-1/p) ≤ 1/(p-1) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hm : 0 < p-1 := by linarith only [hp]
  have hd : 0 < 1-1/p := by
    have hh := (div_lt_one hp0).mpr hp
    linarith only [hh]
  have hh := one_sub_inv_le_log_of_pos hd
  have he : 1-(1-1/p)⁻¹ = -1/(p-1) := by
    field_simp
    ring
  rw [he,neg_div] at hh
  linarith only [hh]

/-- Each modulus at least B supplies at most 1/(B-1) of logarithmic thinning.
This retains the cardinality of the padding, not just its existence. -/
theorem neg_log_product_le_card (R : Finset ℕ) (B : ℕ) (hB : 2 ≤ B)
    (hR : ∀ p ∈ R, B ≤ p) :
    -log (∏ p ∈ R, (1-1/(p : ℝ))) ≤ (R.card : ℝ)/((B : ℝ)-1) := by
  have hB1 : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hp1 (p : ℕ) (hp : p ∈ R) : (1 : ℝ) < p :=
    hB1.trans_le (by exact_mod_cast hR p hp)
  have hf (p : ℕ) (hp : p ∈ R) : (1-1/(p : ℝ)) ≠ 0 := by
    have hp0 : (0 : ℝ) < p := by linarith only [hp1 p hp]
    have hh := (div_lt_one hp0).mpr (hp1 p hp)
    linarith only [hh]
  rw [log_prod hf,← sum_neg_distrib]
  calc
    _ ≤ ∑ p ∈ R, 1/((p : ℝ)-1) :=
      sum_le_sum (fun p hp => neg_log_one_sub_inv_le p (hp1 p hp))
    _ ≤ ∑ _p ∈ R, 1/((B : ℝ)-1) := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (by linarith only [hB1])
        (sub_le_sub_right (by exact_mod_cast hR p hp) 1)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

/-- Approximating a Laplace parameter t by thinning to density 1-exp(-t)
requires this explicit logarithmic cardinality cost. -/
theorem log_target_le_card_of_dilution (R : Finset ℕ) (B : ℕ) (hB : 2 ≤ B)
    (hR : ∀ p ∈ R, B ≤ p) (t : ℝ) (_ht : 0 < t)
    (hd : (∏ p ∈ R, (1-1/(p : ℝ))) ≤ 1-exp (-t)) :
    -log (1-exp (-t)) ≤ (R.card : ℝ)/((B : ℝ)-1) := by
  have hprod : 0 < ∏ p ∈ R, (1-1/(p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hR p hp; omega)
    have hp0 : (0 : ℝ) < p := by linarith only [hp1]
    have hh := (div_lt_one hp0).mpr hp1
    linarith only [hh]
  exact (neg_le_neg (log_le_log hprod hd)).trans (neg_log_product_le_card R B hB hR)

/-- At most B moduli, all at least B, leave density at least exp(-2). -/
theorem exp_neg_two_le_product_of_card_le (R : Finset ℕ) (B : ℕ)
    (hB : 2 ≤ B) (hR : ∀ p ∈ R, B ≤ p) (hcard : R.card ≤ B) :
    exp (-2 : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)) := by
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : 0 < (B : ℝ)-1 := by linarith only [hB2]
  have hc : (R.card : ℝ)/((B : ℝ)-1) ≤ 2 := by
    apply (div_le_iff₀ hB0).mpr
    have hh : (R.card : ℝ) ≤ B := by exact_mod_cast hcard
    linarith only [hh,hB2]
  have hl := (neg_log_product_le_card R B hB hR).trans hc
  have hprod : 0 < ∏ p ∈ R, (1-1/(p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by have := hR p hp; omega)
    have hp0 : (0 : ℝ) < p := by linarith only [hp1]
    have hh := (div_lt_one hp0).mpr hp1
    linarith only [hh]
  have hh := exp_le_exp.mpr (show (-2 : ℝ) ≤ log (∏ p ∈ R, (1-1/(p : ℝ))) by linarith only [hl])
  simpa only [exp_log hprod] using hh

/-- Bounded-cardinality large-modulus padding cannot realize sufficiently
small Laplace parameters. The statement is about this padding scheme only. -/
theorem no_small_parameter_bounded_padding (B : ℕ) (hB : 2 ≤ B)
    (t : ℝ) (ht : t < exp (-2 : ℝ)) :
    ¬∃ R : Finset ℕ, R.card ≤ B ∧ (∀ p ∈ R, B ≤ p) ∧
      (∏ p ∈ R, (1-1/(p : ℝ))) ≤ 1-exp (-t) := by
  rintro ⟨R,hcard,hR,hd⟩
  have hh := (exp_neg_two_le_product_of_card_le R B hB hR hcard).trans hd
  have he := add_one_le_exp (-t)
  linarith only [hh,he,ht]

#print axioms neg_log_product_le_card
#print axioms log_target_le_card_of_dilution
#print axioms exp_neg_two_le_product_of_card_le
#print axioms no_small_parameter_bounded_padding
end Erdos970.PrimeDilution
