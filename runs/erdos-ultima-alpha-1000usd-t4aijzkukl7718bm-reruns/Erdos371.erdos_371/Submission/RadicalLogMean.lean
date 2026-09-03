import FormalConjecturesUtil
import Submission.PrimeLogMass
import Submission.AffinePrimeOccurrenceExcess

/-! Normalized logarithms of radicals converge to one in mean. -/

namespace Erdos371RadicalLogMean

open Finset Filter
open scoped Topology

noncomputable def radLog (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, Real.log (p : ℝ)

lemma radLog_nonneg (n : ℕ) : 0 ≤ radLog n := by
  exact sum_nonneg fun p _ => Real.log_natCast_nonneg p

@[simp] lemma radLog_zero : radLog 0 = 0 := by simp [radLog]

lemma radLog_le_log {n : ℕ} (hn : 0 < n) : radLog n ≤ Real.log (n : ℝ) := by
  have hp : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have he : radLog n = Real.log ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    · rfl
    · intro p hp
      exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [he]
  exact Real.log_le_log (Nat.cast_pos.mpr hp)
    (Nat.cast_le.mpr (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)))

lemma radLog_le_cutoff {N n : ℕ} (hN : 1 < N) (hn : n ≤ N) :
    radLog n ≤ Real.log (N : ℝ) := by
  by_cases h0 : n = 0
  · simp [h0, Real.log_natCast_nonneg]
  · exact (radLog_le_log (Nat.pos_of_ne_zero h0)).trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0) (Nat.cast_le.mpr hn))

lemma sum_radLog (N : ℕ) :
    (∑ n ∈ range N, radLog (n+1)) =
      ∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ) * (N/p : ℕ) := by
  have h := Erdos371AffinePrimeOccurrenceExcess.sum_primeWeight_expand
    (fun p => Real.log (p : ℝ)) (fun n => n+1)
    (A := N) (X := N) (by intro n hn; dsimp; exact ⟨by omega, by omega⟩)
  simpa only [Erdos371AffinePrimeOccurrenceExcess.primeWeight, radLog, Nat.card_multiples] using h

lemma cast_div_lower {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (N : ℝ)/p - 1 ≤ (N/p : ℕ) := by
  have hh : N < (N/p+1)*p := by
    have := Nat.mod_lt N hp
    have := Nat.mod_add_div N p
    nlinarith
  have hh' : (N : ℝ) < ((N/p : ℕ) + 1 : ℝ) * p := by exact_mod_cast hh
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have := (div_lt_iff₀ hp').mpr hh'
  linarith

noncomputable def level (N n : ℕ) : ℝ := radLog n / Real.log (N : ℝ)

lemma level_bounds {N : ℕ} (hN : 1 < N) {n : ℕ} (hn : n ≤ N) :
    0 ≤ level N n ∧ level N n ≤ 1 := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  exact ⟨div_nonneg (radLog_nonneg n) hl.le,
    (div_le_one hl).mpr (radLog_le_cutoff hN hn)⟩

lemma sum_level_lower {N : ℕ} (hN : 1 < N) :
    (N : ℝ) * (Erdos371PrimeLogMass.mass N / Real.log N) - Nat.primeCounting N ≤
      ∑ n ∈ range N, level N (n+1) := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  unfold level
  rw [← sum_div, sum_radLog, sum_div]
  calc
    _ = ∑ p ∈ (N+1).primesBelow,
        (Real.log (p : ℝ) * ((N : ℝ)/p) / Real.log N - 1) := by
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one,
        Nat.primesBelow_card_eq_primeCounting']
      congr 1
      unfold Erdos371PrimeLogMass.mass
      rw [sum_div, mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN,hp⟩ := Nat.mem_primesBelow.mp hp
      have hc := cast_div_lower hp.pos N
      have hlog := Real.log_natCast_nonneg p
      have hlogN : Real.log (p : ℝ) / Real.log N ≤ 1 := by
        apply (div_le_one hl).mpr
        exact Real.log_le_log (Nat.cast_pos.mpr hp.pos) (by exact_mod_cast (by omega : p ≤ N))
      have hh := mul_le_mul_of_nonneg_left hc (div_nonneg hlog hl.le)
      calc
        _ = (Real.log (p : ℝ) / Real.log N) * ((N : ℝ)/p) - 1 := by ring
        _ ≤ (Real.log (p : ℝ) / Real.log N) * ((N : ℝ)/p - 1) := by nlinarith
        _ ≤ _ := by convert hh using 1 <;> ring

lemma mean_level_tendsto_one :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, level N (n+1)) / N) atTop (𝓝 1) := by
  have hlow : Tendsto (fun N : ℕ =>
      Erdos371PrimeLogMass.mass N / Real.log N - (Nat.primeCounting N : ℝ)/N)
      atTop (𝓝 1) := by
    simpa using Erdos371PrimeLogMass.mass_log_ratio_tendsto_one.sub
      Erdos371CofactorDensity.primeCounting_ratio_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hh := div_le_div_of_nonneg_right (sum_level_lower hN) hn.le
    simpa [sub_div, hn.ne'] using hh
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    apply (div_le_one hn).mpr
    calc
      _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum fun n hn =>
        (level_bounds hN (by have := mem_range.mp hn; omega)).2
      _ = _ := by simp

noncomputable def defect (N : ℕ) : ℝ := ∑ n ∈ range (N+1), (1-level N n)

lemma defect_nonneg {N : ℕ} (hN : 1 < N) : 0 ≤ defect N := by
  exact sum_nonneg fun n hn => sub_nonneg.mpr
    (level_bounds hN (by have := mem_range.mp hn; omega)).2

lemma defect_eq (N : ℕ) :
    defect N = 1 + (N : ℝ) - ∑ n ∈ range N, level N (n+1) := by
  unfold defect
  rw [sum_range_succ']
  simp [level, sum_sub_distrib]
  ring

/-- Mean absolute deviation from one over the entire cutoff interval vanishes. -/
theorem defect_mean_tendsto_zero :
    Tendsto (fun N : ℕ => defect N / N) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 1/(N : ℝ) + (1 -
      (∑ n ∈ range N, level N (n+1))/N)) atTop (𝓝 (0+(1-1))) :=
    tendsto_one_div_atTop_nhds_zero_nat.add
      (tendsto_const_nhds.sub mean_level_tendsto_one)
  norm_num only [sub_self, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [defect_eq]
  field_simp
  <;> ring

end Erdos371RadicalLogMean

#print axioms Erdos371RadicalLogMean.defect_mean_tendsto_zero
