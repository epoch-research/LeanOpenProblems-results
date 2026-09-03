import Submission.AdjacentThresholdExpansion
import Submission.SmoothCutoffSkew

/-! The neighboring quantized thresholds are exact moving smoothness cutoffs.
The top threshold contributes only a telescoping endpoint term. -/
namespace Erdos371
open Finset Filter FiniteInformation FixedPrimeAvoidance
open scoped Topology

noncomputable def strictPowerCutoff (Q N t : ℕ) : ℕ :=
  ⌈(N : ℝ)^((t+1 : ℝ)/Q)⌉₊-1

lemma quantThreshold_le_iff_log (Q N t n : ℕ) (hN : 1 < N) (ht : t < Q) :
    (primeQuantLabel Q N n).val ≤ t ↔
      (Q : ℝ)*normalizedPrimeLog N n < (t+1 : ℝ) := by
  change min Q ⌊(Q : ℝ)*normalizedPrimeLog N n⌋₊ ≤ t ↔ _
  have he : min Q ⌊(Q : ℝ)*normalizedPrimeLog N n⌋₊ ≤ t ↔
      ⌊(Q : ℝ)*normalizedPrimeLog N n⌋₊ < t+1 := by omega
  have hnon : 0 ≤ normalizedPrimeLog N n :=
    div_nonneg (primeLog_nonneg n) (Real.log_pos (by exact_mod_cast hN)).le
  rw [he,Nat.floor_lt (mul_nonneg (Nat.cast_nonneg Q) hnon)]
  push_cast
  rfl

lemma quantThreshold_le_iff_power (Q N t n : ℕ) (hN : 1 < N) (ht : t < Q) :
    (primeQuantLabel Q N n).val ≤ t ↔
      (Nat.maxPrimeFac n : ℝ) < (N : ℝ)^((t+1 : ℝ)/Q) := by
  rw [quantThreshold_le_iff_log Q N t n hN ht]
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hpow := Real.rpow_pos_of_pos hNr ((t+1 : ℝ)/Q)
  by_cases hn : n=0
  · subst n
    simp only [normalizedPrimeLog,primeLog_zero,zero_div,mul_zero,Nat.maxPrimeFac_zero,Nat.cast_zero]
    exact iff_of_true (by positivity) hpow
  have hp : (0 : ℝ) < Nat.maxPrimeFac n := by
    exact_mod_cast maxPrimeFac_pos_of_pos n (by omega)
  rw [← Real.log_lt_log_iff hp hpow,Real.log_rpow hNr]
  unfold normalizedPrimeLog primeLog
  rw [← mul_div_assoc,div_lt_iff₀ hlog]
  rw [div_mul_eq_mul_div]
  constructor <;> intro h
  · apply (lt_div_iff₀ hQr).mpr
    nlinarith
  · have hh := (lt_div_iff₀ hQr).mp h
    nlinarith

lemma strictPowerCutoff_pos (Q N t : ℕ) (hQ : 0 < Q) (hN : 1 < N) :
    1 ≤ strictPowerCutoff Q N t := by
  have hexp : (0 : ℝ) < (t+1 : ℝ)/Q := by positivity
  have hpow : (1 : ℝ) < (N : ℝ)^((t+1 : ℝ)/Q) :=
    Real.one_lt_rpow (by exact_mod_cast hN) hexp
  have hh : 1 < ⌈(N : ℝ)^((t+1 : ℝ)/Q)⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hpow)
  unfold strictPowerCutoff
  omega

lemma quantThreshold_eq_smooth (Q N t n : ℕ) (hN : 1 < N) (ht : t < Q) :
    quantThreshold Q N t n = smoothIndicator (strictPowerCutoff Q N t) n := by
  have hpos := strictPowerCutoff_pos Q N t (by omega) hN
  have he : (primeQuantLabel Q N n).val ≤ t ↔ Nat.maxPrimeFac n ≤ strictPowerCutoff Q N t := by
    rw [quantThreshold_le_iff_power Q N t n hN ht,← Nat.lt_ceil]
    unfold strictPowerCutoff at hpos ⊢
    omega
  simp only [quantThreshold,thresholdStep,smoothIndicator,he]

lemma quantThreshold_top (Q N n : ℕ) : quantThreshold Q N Q n = 1 := by
  unfold quantThreshold thresholdStep
  exact if_pos (Nat.le_of_lt_succ (primeQuantLabel Q N n).isLt)

lemma quantNeighborSkew_top (Q N n : ℕ) (hQ : 0 < Q) :
    quantNeighborSkew Q N (Q-1) n = quantThreshold Q N (Q-1) n-quantThreshold Q N (Q-1) (n+1) := by
  simp only [quantNeighborSkew,pairSkew,Nat.sub_add_cancel hQ,quantThreshold_top,mul_one,one_mul]

lemma quantNeighborSkew_top_sum (Q N : ℕ) (hQ : 0 < Q) :
    (∑ n ∈ range N, quantNeighborSkew Q N (Q-1) n) =
      quantThreshold Q N (Q-1) 0-quantThreshold Q N (Q-1) N := by
  simp_rw [quantNeighborSkew_top Q N _ hQ]
  exact sum_range_sub' (quantThreshold Q N (Q-1)) N

lemma quantNeighborSkew_eq_smooth_point (Q N t n : ℕ) (hN : 1 < N) (ht : t+1 < Q) :
    quantNeighborSkew Q N t n =
      smoothIndicator (strictPowerCutoff Q N t) n*smoothIndicator (strictPowerCutoff Q N (t+1)) (n+1)-
      smoothIndicator (strictPowerCutoff Q N (t+1)) n*smoothIndicator (strictPowerCutoff Q N t) (n+1) := by
  simp only [quantNeighborSkew,pairSkew,quantThreshold_eq_smooth Q N t _ hN (by omega),
    quantThreshold_eq_smooth Q N (t+1) _ hN ht]

/-- Shifting the sample by one integer is the only difference between an
interior neighboring-threshold mean and the earlier smooth-cutoff kernel. -/
lemma quantNeighborSkew_smooth_sum (Q N t : ℕ) (hN : 1 < N) (ht : t+1 < Q) :
    (∑ n ∈ range N, quantNeighborSkew Q N t n) =
      smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N-
      quantNeighborSkew Q N t N := by
  have he := sum_range_succ' (quantNeighborSkew Q N t) N
  rw [sum_range_succ] at he
  have hzero : quantNeighborSkew Q N t 0 = 0 := by
    rw [quantNeighborSkew_eq_smooth_point Q N t 0 hN ht]
    simp [smoothIndicator,strictPowerCutoff_pos Q N t (by omega) hN,
      strictPowerCutoff_pos Q N (t+1) (by omega) hN]
  have hshift : (∑ n ∈ range N, quantNeighborSkew Q N t (n+1)) =
      smoothCutoffSkew (strictPowerCutoff Q N t) (strictPowerCutoff Q N (t+1)) N := by
    unfold smoothCutoffSkew
    apply sum_congr rfl
    intro n _
    simpa only [Nat.add_assoc] using quantNeighborSkew_eq_smooth_point Q N t (n+1) hN ht
  rw [hzero,hshift,add_zero] at he
  linarith

#print axioms quantThreshold_eq_smooth
#print axioms quantNeighborSkew_smooth_sum
end Erdos371
