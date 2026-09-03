import Submission.DoubleCoverPairFamily
import Submission.PrimeSetMertens
import Submission.SymmetricIsolation

/-! Analytic estimates for four selected reciprocal-prime bands. -/
namespace Erdos970.DoubleCover
open Finset Real WeightedMertens Filter

lemma log_six_fifths_le : log ((6 : ℝ) / 5) ≤ 183 / 1000 := by
  have h := sum_range_sub_log_div_le (x := (1 / 11 : ℝ)) (by norm_num) 3
  norm_num [sum_range_succ] at h
  linarith [(abs_le.mp h).2]

lemma log_five_fourths_le : log ((5 : ℝ) / 4) ≤ 224 / 1000 := by
  have h := sum_range_sub_log_div_le (x := (1 / 9 : ℝ)) (by norm_num) 3
  norm_num [sum_range_succ] at h
  linarith [(abs_le.mp h).2]

lemma log_five_thirds_le : log ((5 : ℝ) / 3) ≤ 511 / 1000 := by
  have h := sum_range_sub_log_div_le (x := (1 / 4 : ℝ)) (by norm_num) 3
  norm_num [sum_range_succ] at h
  linarith [(abs_le.mp h).2]

lemma band_reciprocal_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t u v : ℕ) (ht : 2 ≤ t) (hu : 0 < u) (huv : u ≤ v)
    (hl : 2000 * (boundConstant + 1) ≤ log (t : ℝ)) :
    (∑ p ∈ P.filter (fun p => t ^ u < p ∧ p ≤ t ^ v), 1 / (p : ℝ)) ≤
      log ((v : ℝ) / u) + 1 / 1000 := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlog : 0 < log (t : ℝ) := log_pos (by linarith)
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hlogu : 0 < log ((t : ℝ) ^ u) := by rw [log_pow]; positivity
  have hlogv : 0 < log ((t : ℝ) ^ v) := by
    rw [log_pow]
    have hvR : (0 : ℝ) < v := by exact_mod_cast (lt_of_lt_of_le hu huv)
    positivity
  have ha : 2 ≤ (t : ℝ) ^ u := by
    exact htR.trans (by simpa using pow_le_pow_right₀ ht1 hu)
  have hab : (t : ℝ) ^ u ≤ (t : ℝ) ^ v := pow_le_pow_right₀ ht1 huv
  have hs : (∑ p ∈ P.filter (fun p => t ^ u < p ∧ p ≤ t ^ v), 1 / (p : ℝ)) ≤
      reciprocalInterval ((t : ℝ) ^ u) ((t : ℝ) ^ v) := by
    unfold reciprocalInterval
    simp only [one_div, ← Nat.cast_pow, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpP, hpu, hpv⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by simpa using hpu, by simpa using hpv⟩, hP p hpP⟩
    · intro p hp hn
      positivity
  have h := (abs_le.mp (abs_reciprocalInterval_sub_loglog ha hab)).2
  have he : log (log ((t : ℝ) ^ v)) - log (log ((t : ℝ) ^ u)) = log ((v : ℝ) / u) := by
    rw [← log_div hlogv.ne' hlogu.ne']
    congr 1
    simp only [log_pow]
    field_simp
  have herr : 2 * (boundConstant + 1) / log ((t : ℝ) ^ u) ≤ 1 / 1000 := by
    apply (div_le_iff₀ hlogu).mpr
    rw [log_pow]
    have hh := mul_le_mul_of_nonneg_right huR hlog.le
    nlinarith only [hl, hh]
  rw [he] at h
  linarith

lemma four_band_caps (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℕ) (ht : 2 ≤ t)
    (hl : 2000 * (boundConstant + 1) ≤ log (t : ℝ)) :
    (∑ p ∈ P.filter (fun p => t ^ 10 < p ∧ p ≤ t ^ 12), 1 / (p : ℝ)) ≤ 184 / 1000 ∧
    (∑ p ∈ P.filter (fun p => t ^ 12 < p ∧ p ≤ t ^ 15), 1 / (p : ℝ)) ≤ 225 / 1000 ∧
    (∑ p ∈ P.filter (fun p => t ^ 15 < p ∧ p ≤ t ^ 18), 1 / (p : ℝ)) ≤ 184 / 1000 ∧
    (∑ p ∈ P.filter (fun p => t ^ 18 < p ∧ p ≤ t ^ 30), 1 / (p : ℝ)) ≤ 512 / 1000 := by
  have ha := band_reciprocal_le P hP t 10 12 ht (by omega) (by omega) hl
  have hb := band_reciprocal_le P hP t 12 15 ht (by omega) (by omega) hl
  have hc := band_reciprocal_le P hP t 15 18 ht (by omega) (by omega) hl
  have hd := band_reciprocal_le P hP t 18 30 ht (by omega) (by omega) hl
  norm_num only [Nat.cast_ofNat, show (12 : ℝ) / 10 = 6 / 5 by norm_num,
    show (15 : ℝ) / 12 = 5 / 4 by norm_num, show (18 : ℝ) / 15 = 6 / 5 by norm_num,
    show (30 : ℝ) / 18 = 5 / 3 by norm_num] at ha hb hc hd
  exact ⟨by linarith [log_six_fifths_le], by linarith [log_five_fourths_le],
    by linarith [log_six_fifths_le], by linarith [log_five_thirds_le]⟩

lemma exists_prime_count_threshold : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((n + 1).primesBelow.card : ℝ) ≤ (n : ℝ) / 100 := by
  have he := PrimeCountingDyadic.density_tendsto_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop 1))
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨h, hn1⟩ := hN n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hcard : (n + 1).primesBelow.card = n.primeCounting := by
    simp only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hcard]
  have hh := (div_lt_iff₀ hnR).mp h
  linarith

#print axioms four_band_caps
#print axioms exists_prime_count_threshold
end Erdos970.DoubleCover
