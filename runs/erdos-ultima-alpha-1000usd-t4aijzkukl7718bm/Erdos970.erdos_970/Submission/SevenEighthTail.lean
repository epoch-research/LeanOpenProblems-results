import Submission.PrimeSetMertens

/-! Reciprocal mass above a seven-eighths cardinality cutoff. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma log_eight_sevenths_le : log ((8 : ℝ) / 7) ≤ 7 / 50 := by
  have hh := log_le_log (by norm_num : (0 : ℝ) < 8 / 7)
    (by norm_num : (8 : ℝ) / 7 ≤ (107 / 100) ^ 2)
  rw [log_pow] at hh
  have hl := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 107 / 100)
  norm_num at hh hl ⊢
  linarith

/-- At most t^8 primes have reciprocal mass <=1/7 beyond D*t^7,
provided D is one sufficiently large absolute constant. -/
theorem tail_seven_eighths (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t D : ℕ) (ht : 0 < t) (hD : 1024 ≤ D)
    (hlogD : 2048 * (boundConstant + 1) ≤ log (D : ℝ))
    (hcard : P.card ≤ t ^ 8) :
    (∑ p ∈ P.filter (fun p => D * t ^ 7 < p), 1 / (p : ℝ)) ≤ 1 / 7 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have ha : (2 : ℝ) ≤ (D : ℝ) * t ^ 7 := by
    have hp : (1 : ℝ) ≤ (t : ℝ) ^ 7 := one_le_pow₀ ht1
    have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
    nlinarith
  have hab : (D : ℝ) * t ^ 7 ≤ (D : ℝ) * t ^ 8 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega : 7 ≤ 8)) hD0.le
  have hla : log ((D : ℝ) * t ^ 7) = log D + 7 * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num
  have hlb : log ((D : ℝ) * t ^ 8) = log D + 8 * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num
  have hld : 0 ≤ log (D : ℝ) := log_nonneg hD1
  have hlt : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hla0 : 0 < log ((D : ℝ) * t ^ 7) := log_pos (by linarith)
  have hlb0 : 0 < log ((D : ℝ) * t ^ 8) := log_pos (by linarith)
  have hratio : log ((D : ℝ) * t ^ 8) / log ((D : ℝ) * t ^ 7) ≤ 8 / 7 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla, hlb]
    linarith
  have hlogratio : log (log ((D : ℝ) * t ^ 8)) - log (log ((D : ℝ) * t ^ 7)) ≤ 7 / 50 := by
    rw [← log_div hlb0.ne' hla0.ne']
    exact (log_le_log (div_pos hlb0 hla0) hratio).trans log_eight_sevenths_le
  have herr : 2 * (boundConstant + 1) / log ((D : ℝ) * t ^ 7) ≤ 1 / 1024 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla]
    linarith
  have hbudget : (P.card : ℝ) / ((D : ℝ) * t ^ 8) ≤ 1 / 1024 := by
    apply (div_le_iff₀ (show 0 < (D : ℝ) * t ^ 8 by positivity)).mpr
    have hcardR : (P.card : ℝ) ≤ (t : ℝ) ^ 8 := by exact_mod_cast hcard
    have hD1024 : (1024 : ℝ) ≤ D := by exact_mod_cast hD
    have hh := mul_le_mul_of_nonneg_right hD1024 (pow_nonneg ht0.le 8)
    linarith
  have hh := prime_set_tail P hP ha hab
  have hfilter : P.filter (fun p : ℕ => (D : ℝ) * t ^ 7 < (p : ℝ)) =
      P.filter (fun p => D * t ^ 7 < p) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, by exact_mod_cast hlt⟩
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, by exact_mod_cast hlt⟩
  rw [hfilter] at hh
  simp only [one_div] at ⊢
  linarith

#print axioms tail_seven_eighths
end Erdos970.WeightedMertens
