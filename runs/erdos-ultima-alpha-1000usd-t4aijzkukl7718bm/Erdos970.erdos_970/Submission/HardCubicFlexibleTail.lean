import Submission.ThreeQuarterTail

/-! A flexible cutoff for the existing hard-cubic reciprocal budget. The
explicit exponent below is slightly less than three quarters, not one half. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma log_improved_cubic_ratio :
    log ((200000 : ℝ) / 149999) ≤ 287697 / 1000000 := by
  have he : log ((200000 : ℝ) / 149999) =
      log (4 / 3 : ℝ) + log (150000 / 149999 : ℝ) := by
    rw [← log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0)
      (by norm_num : (150000 / 149999 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 150000 / 149999)
  rw [he]
  linarith only [hh, log_four_thirds_le_cubic_tail]

/-- The proof retains the exact ratio of the two power exponents. -/
theorem tail_power_ratio (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (e f t D : ℕ) (he : 0 < e) (hef : e ≤ f) (ht : 0 < t)
    (hD : 1000000 ≤ D)
    (hlogD : 2000000 * (boundConstant + 1) ≤ log (D : ℝ))
    (hratioBound : log ((f : ℝ) / e) ≤ 287697 / 1000000)
    (hcard : P.card ≤ t ^ f) :
    (∑ p ∈ P.filter (fun p => D * t ^ e < p), 1 / (p : ℝ)) ≤ 2877 / 10000 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hefR : (e : ℝ) ≤ f := by exact_mod_cast hef
  have ha : (2 : ℝ) ≤ (D : ℝ) * t ^ e := by
    have hp : (1 : ℝ) ≤ (t : ℝ) ^ e := one_le_pow₀ ht1
    have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
    nlinarith
  have hab : (D : ℝ) * t ^ e ≤ (D : ℝ) * t ^ f :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 hef) hD0.le
  have hla : log ((D : ℝ) * t ^ e) = log D + e * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
  have hlb : log ((D : ℝ) * t ^ f) = log D + f * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
  have hld : 0 ≤ log (D : ℝ) := log_nonneg hD1
  have hlt : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hla0 : 0 < log ((D : ℝ) * t ^ e) := log_pos (by linarith)
  have hlb0 : 0 < log ((D : ℝ) * t ^ f) := log_pos (by linarith)
  have hratio : log ((D : ℝ) * t ^ f) / log ((D : ℝ) * t ^ e) ≤ (f : ℝ) / e := by
    apply (div_le_div_iff₀ hla0 he0).mpr
    rw [hla, hlb]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hefR) hld]
  have hlogratio : log (log ((D : ℝ) * t ^ f)) - log (log ((D : ℝ) * t ^ e)) ≤
      287697 / 1000000 := by
    rw [← log_div hlb0.ne' hla0.ne']
    exact (log_le_log (div_pos hlb0 hla0) hratio).trans hratioBound
  have herr : 2 * (boundConstant + 1) / log ((D : ℝ) * t ^ e) ≤ 1 / 1000000 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla]
    have hx := mul_nonneg he0.le hlt
    linarith only [hlogD, hx]
  have hbudget : (P.card : ℝ) / ((D : ℝ) * t ^ f) ≤ 1 / 1000000 := by
    apply (div_le_iff₀ (show 0 < (D : ℝ) * t ^ f by positivity)).mpr
    have hcardR : (P.card : ℝ) ≤ (t : ℝ) ^ f := by exact_mod_cast hcard
    have hD1000000 : (1000000 : ℝ) ≤ D := by exact_mod_cast hD
    have hh := mul_le_mul_of_nonneg_right hD1000000 (pow_nonneg ht0.le f)
    linarith only [hh, hcardR]
  have hh := prime_set_tail P hP ha hab
  have hfilter : P.filter (fun p : ℕ => (D : ℝ) * t ^ e < (p : ℝ)) =
      P.filter (fun p => D * t ^ e < p) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, by exact_mod_cast hlt⟩
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, by exact_mod_cast hlt⟩
  rw [hfilter] at hh
  simp only [one_div] at ⊢
  linarith only [hh, hlogratio, herr, hbudget]

#print axioms log_improved_cubic_ratio
#print axioms tail_power_ratio
end Erdos970.WeightedMertens
