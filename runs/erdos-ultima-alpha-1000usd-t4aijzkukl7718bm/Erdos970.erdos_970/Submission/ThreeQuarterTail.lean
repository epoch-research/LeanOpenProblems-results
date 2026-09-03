import Submission.PrimeSetMertens

/-! Reciprocal mass above a three-quarters cardinality cutoff. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma log_four_thirds_le_cubic_tail : log ((4 : ℝ) / 3) ≤ 28769 / 100000 := by
  have hh := sum_range_sub_log_div_le (x := (1 / 7 : ℝ)) (by norm_num) 3
  norm_num [sum_range_succ] at hh
  have hu := (abs_le.mp hh).2
  linarith

/-- At most t^4 primes have reciprocal mass <=2877/10000 beyond D*t^3,
provided D is one sufficiently large absolute constant. -/
theorem tail_three_quarters (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t D : ℕ) (ht : 0 < t) (hD : 1000000 ≤ D)
    (hlogD : 2000000 * (boundConstant + 1) ≤ log (D : ℝ))
    (hcard : P.card ≤ t ^ 4) :
    (∑ p ∈ P.filter (fun p => D * t ^ 3 < p), 1 / (p : ℝ)) ≤ 2877 / 10000 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have ha : (2 : ℝ) ≤ (D : ℝ) * t ^ 3 := by
    have hp : (1 : ℝ) ≤ (t : ℝ) ^ 3 := one_le_pow₀ ht1
    have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
    nlinarith
  have hab : (D : ℝ) * t ^ 3 ≤ (D : ℝ) * t ^ 4 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega : 3 ≤ 4)) hD0.le
  have hla : log ((D : ℝ) * t ^ 3) = log D + 3 * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num
  have hlb : log ((D : ℝ) * t ^ 4) = log D + 4 * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num
  have hld : 0 ≤ log (D : ℝ) := log_nonneg hD1
  have hlt : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hla0 : 0 < log ((D : ℝ) * t ^ 3) := log_pos (by linarith)
  have hlb0 : 0 < log ((D : ℝ) * t ^ 4) := log_pos (by linarith)
  have hratio : log ((D : ℝ) * t ^ 4) / log ((D : ℝ) * t ^ 3) ≤ 4 / 3 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla, hlb]
    linarith
  have hlogratio : log (log ((D : ℝ) * t ^ 4)) - log (log ((D : ℝ) * t ^ 3)) ≤ 28769 / 100000 := by
    rw [← log_div hlb0.ne' hla0.ne']
    exact (log_le_log (div_pos hlb0 hla0) hratio).trans log_four_thirds_le_cubic_tail
  have herr : 2 * (boundConstant + 1) / log ((D : ℝ) * t ^ 3) ≤ 1 / 1000000 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla]
    linarith
  have hbudget : (P.card : ℝ) / ((D : ℝ) * t ^ 4) ≤ 1 / 1000000 := by
    apply (div_le_iff₀ (show 0 < (D : ℝ) * t ^ 4 by positivity)).mpr
    have hcardR : (P.card : ℝ) ≤ (t : ℝ) ^ 4 := by exact_mod_cast hcard
    have hD1000000 : (1000000 : ℝ) ≤ D := by exact_mod_cast hD
    have hh := mul_le_mul_of_nonneg_right hD1000000 (pow_nonneg ht0.le 4)
    linarith
  have hh := prime_set_tail P hP ha hab
  have hfilter : P.filter (fun p : ℕ => (D : ℝ) * t ^ 3 < (p : ℝ)) =
      P.filter (fun p => D * t ^ 3 < p) := by
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

#print axioms tail_three_quarters
end Erdos970.WeightedMertens
