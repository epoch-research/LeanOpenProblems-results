import Submission.QuadraticDampingMean
import Submission.BothLargePrimeLower

/-! The actual quadratic large-product tail cannot be removed by an absolute
mean estimate: its mean multiplicity has a positive lower bound. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma bothAbove_has_largeCrossPrimePair (B N n : ℕ) (hB : 1 ≤ B) (hN : 1 < N)
    (hsize : 2*N ≤ (B+1)^2) (hn : n ∈ bothAboveSet B N) :
    1 ≤ (largeCrossPrimePairs (N+1) n).card := by
  obtain ⟨hnN,hp,hq⟩ := mem_filter.mp hn
  have hn1 : 1 < n := (Nat.one_lt_maxPrimeFac_iff n).mp (by omega)
  have hnp : n ≠ 0 := by omega
  apply card_pos.mpr
  apply Exists.intro (Nat.maxPrimeFac n,Nat.maxPrimeFac (n+1))
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨?_,?_⟩,?_⟩
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn1,Nat.maxPrimeFac_dvd,hnp⟩
  · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),
      Nat.maxPrimeFac_dvd,by omega⟩
  · have hh := Nat.mul_le_mul (show B+1 ≤ Nat.maxPrimeFac n by omega)
      (show B+1 ≤ Nat.maxPrimeFac (n+1) by omega)
    change N+1 < Nat.maxPrimeFac n*Nat.maxPrimeFac (n+1)
    nlinarith

lemma largeCrossPrimePairs_shifted_sum_ge (N : ℕ) :
    (∑ n ∈ range N, ((largeCrossPrimePairs (N+1) n).card : ℝ)) ≤
      ∑ n ∈ range N, ((largeCrossPrimePairs (N+1) (n+1)).card : ℝ) := by
  have he := sum_range_succ' (fun n => ((largeCrossPrimePairs (N+1) n).card : ℝ)) N
  rw [sum_range_succ] at he
  have hz : (largeCrossPrimePairs (N+1) 0).card=0 := by simp [largeCrossPrimePairs]
  rw [hz,Nat.cast_zero,add_zero] at he
  linarith [Nat.cast_nonneg (α := ℝ) (largeCrossPrimePairs (N+1) N).card]

/-- Positive mass remains in exactly the quadratic range which has not
been estimated with its sign. -/
theorem largeCrossPrimePairs_mean_positive :
    ∀ᶠ N : ℕ in atTop, (1/20 : ℝ) ≤
      (∑ n ∈ range N, ((largeCrossPrimePairs (N+1) (n+1)).card : ℝ))/N := by
  filter_upwards [bothAbove_upperHalf_positive_proportion,
    ceilPowerCutoff_upperHalf_product_eventually,eventually_gt_atTop (1 : ℕ)] with N hp hsize hN
  let B := ceilPowerCutoff (21/40) N
  have hB : 1 ≤ B :=
    ((ceilPowerCutoff_data (21/40) (3/4) (by norm_num) (by norm_num) (by norm_num) N hN).1).le
  have hc : ((bothAboveSet B N).card : ℝ) ≤
      ∑ n ∈ range N, ((largeCrossPrimePairs (N+1) n).card : ℝ) := by
    calc
      _ = ∑ _n ∈ bothAboveSet B N, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ bothAboveSet B N, ((largeCrossPrimePairs (N+1) n).card : ℝ) := by
        apply sum_le_sum
        intro n hn
        exact_mod_cast bothAbove_has_largeCrossPrimePair B N n hB hN hsize hn
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun n _ _ => Nat.cast_nonneg _)
  exact hp.trans (div_le_div_of_nonneg_right (hc.trans (largeCrossPrimePairs_shifted_sum_ge N))
    (Nat.cast_nonneg N))

lemma largeCrossPrimePairs_weighted_abs (N n : ℕ) :
    |(largeCrossPrimePairs N n).card*factorSign n|=(largeCrossPrimePairs N n).card := by
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  have hs : |factorSign n|=1 := by
    simp only [factorSign,predicateSign]; split_ifs <;> norm_num
  rw [hs,mul_one]

/-- This disproves only an absolute-tail shortcut, not Erdős 371. -/
theorem quadratic_large_pair_absolute_mean_not_zero :
    ¬Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, |(largeCrossPrimePairs (N+1) (n+1)).card*factorSign (n+1)|)/N)
      atTop (𝓝 0) := by
  intro ht
  simp_rw [largeCrossPrimePairs_weighted_abs] at ht
  obtain ⟨N,hN,hsmall⟩ :=
    (largeCrossPrimePairs_mean_positive.and (ht.eventually_lt_const (by norm_num : (0 : ℝ)<1/40))).exists
  linarith

#print axioms largeCrossPrimePairs_mean_positive
#print axioms quadratic_large_pair_absolute_mean_not_zero
end Erdos371
