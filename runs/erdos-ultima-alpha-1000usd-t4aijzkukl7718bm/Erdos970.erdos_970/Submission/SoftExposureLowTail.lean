import Submission.SoftExposureSymmetric

/-! A lower-tail extension of the core-tail ordered exposure estimate. The
partial-count premise is explicit; the next file supplies it unconditionally
from the verified hard-cubic count theorem. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages

lemma lowCountFraction_nonneg (P : Finset ℕ) (m : ℕ) (b : ℝ) :
    0 ≤ lowCountFraction P m b := by
  unfold lowCountFraction phaseMean
  exact div_nonneg (sum_nonneg (fun r _ => by split_ifs <;> norm_num)) (by positivity)

lemma log_one_sub_fraction_lower (A b : ℝ) (hA : 0 < A) (_hb : 0 ≤ b) (hbA : b ≤ A / 256) :
    -(1 / 128 : ℝ) ≤ log (1 - b / A) := by
  have hfrac : b / A ≤ 1 / 256 := (div_le_iff₀ hA).mpr (by linarith only [hbA])
  have hbase : (128 / 129 : ℝ) ≤ 1 - b / A := by linarith only [hfrac]
  have hpos : 0 < 1 - b / A := lt_of_lt_of_le (by norm_num) hbase
  have hinv : (1 - b / A)⁻¹ ≤ 129 / 128 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 128 / 129) hbase
    norm_num only [one_div, inv_div] at hh
    exact hh
  have hh := one_sub_inv_le_log_of_pos hpos
  linarith only [hh, hinv]

/-- The penalty for allowing b survivors is absorbed by a fixed fraction of
the exposure exponent when b is at most A/256. -/
theorem lowCountFraction_le_core_exponential (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (m n : ℕ) (hn : 0 < n)
    (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b ≤ A / 256)
    (hpartial : ∀ r : Phase P, PartialLower (2 * n) (range m) P (phaseResidues P r) A)
    (hhalf : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 1 / 2) :
    lowCountFraction P m b ≤
      exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ)) - 3 * (n : ℝ) / 64) := by
  have hbA' : b ≤ A := by linarith only [hA, hbA]
  have hh := (lowCountFraction_mul_le_budget P hP m (2 * n) A b hA hb hbA' hpartial).trans
    (budget_le_core_exponential P S hP hS n hn hhalf)
  have hlog := log_one_sub_fraction_lower A b hA hb hbA
  have hbase : 0 < 1 - b / A := by
    have hd : b / A < 1 := (div_lt_one hA).mpr (by linarith only [hA, hbA])
    linarith only [hd]
  have hpow : exp (-(n : ℝ) / 64) ≤ (1 - b / A) ^ (2 * n) := by
    rw [← exp_log hbase, ← exp_nat_mul]
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (n : ℝ) by positivity)
    push_cast
    linarith only [hm]
  have hscaled := (mul_le_mul_of_nonneg_right hpow (lowCountFraction_nonneg P m b)).trans hh
  have he : exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ)) - (n : ℝ) / 16) =
      exp (-(n : ℝ) / 64) * exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ)) - 3 * (n : ℝ) / 64) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he] at hscaled
  exact (mul_le_mul_iff_right₀ (exp_pos _)).mp hscaled

#print axioms lowCountFraction_le_core_exponential
end Erdos970.SoftExposure
