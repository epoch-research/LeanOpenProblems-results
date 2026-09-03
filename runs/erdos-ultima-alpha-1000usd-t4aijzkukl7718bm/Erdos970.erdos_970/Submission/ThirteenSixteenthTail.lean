import Submission.PrimeSetMertens

/-! Reciprocal mass above a thirteen-sixteenths cardinality cutoff. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma log_sixteen_thirteenths_le : log ((16 : ℝ) / 13) ≤ 26 / 125 := by
  have hh := log_le_log (by norm_num : (0 : ℝ) < 16 / 13)
    (by norm_num : (16 : ℝ) / 13 ≤ (4013 / 4000) ^ 64)
  rw [log_pow] at hh
  have hl := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4013 / 4000)
  norm_num at hh hl ⊢
  linarith

/-- At most t^16 primes have reciprocal mass <=5/24 beyond D*t^13,
provided D is one sufficiently large absolute constant. -/
theorem tail_thirteen_sixteenths (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t D : ℕ) (ht : 0 < t) (hD : 65536 ≤ D)
    (hlogD : 131072 * (boundConstant + 1) ≤ log (D : ℝ))
    (hcard : P.card ≤ t ^ 16) :
    (∑ p ∈ P.filter (fun p => D * t ^ 13 < p), 1 / (p : ℝ)) ≤ 5 / 24 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have ha : (2 : ℝ) ≤ (D : ℝ) * t ^ 13 := by
    have hp : (1 : ℝ) ≤ (t : ℝ) ^ 13 := one_le_pow₀ ht1
    have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
    nlinarith
  have hab : (D : ℝ) * t ^ 13 ≤ (D : ℝ) * t ^ 16 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega : 13 ≤ 16)) hD0.le
  have hla : log ((D : ℝ) * t ^ 13) = log D + 13 * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num
  have hlb : log ((D : ℝ) * t ^ 16) = log D + 16 * log t := by
    rw [log_mul hD0.ne' (pow_ne_zero _ ht0.ne'), log_pow]
    norm_num
  have hld : 0 ≤ log (D : ℝ) := log_nonneg hD1
  have hlt : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hla0 : 0 < log ((D : ℝ) * t ^ 13) := log_pos (by linarith)
  have hlb0 : 0 < log ((D : ℝ) * t ^ 16) := log_pos (by linarith)
  have hratio : log ((D : ℝ) * t ^ 16) / log ((D : ℝ) * t ^ 13) ≤ 16 / 13 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla, hlb]
    linarith
  have hlogratio : log (log ((D : ℝ) * t ^ 16)) - log (log ((D : ℝ) * t ^ 13)) ≤ 26 / 125 := by
    rw [← log_div hlb0.ne' hla0.ne']
    exact (log_le_log (div_pos hlb0 hla0) hratio).trans log_sixteen_thirteenths_le
  have herr : 2 * (boundConstant + 1) / log ((D : ℝ) * t ^ 13) ≤ 1 / 65536 := by
    apply (div_le_iff₀ hla0).mpr
    rw [hla]
    linarith
  have hbudget : (P.card : ℝ) / ((D : ℝ) * t ^ 16) ≤ 1 / 65536 := by
    apply (div_le_iff₀ (show 0 < (D : ℝ) * t ^ 16 by positivity)).mpr
    have hcardR : (P.card : ℝ) ≤ (t : ℝ) ^ 16 := by exact_mod_cast hcard
    have hD65536 : (65536 : ℝ) ≤ D := by exact_mod_cast hD
    have hh := mul_le_mul_of_nonneg_right hD65536 (pow_nonneg ht0.le 16)
    linarith
  have hh := prime_set_tail P hP ha hab
  have hfilter : P.filter (fun p : ℕ => (D : ℝ) * t ^ 13 < (p : ℝ)) =
      P.filter (fun p => D * t ^ 13 < p) := by
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

#print axioms tail_thirteen_sixteenths
end Erdos970.WeightedMertens
