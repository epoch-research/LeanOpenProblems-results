import FormalConjecturesUtil
import Submission.PositiveCorrelationGrowth
import Submission.ProductEnergyTransport

/-! The positive same-winner pairs whose product transport stays in a linear
range have only divisor-summatory size. The complementary positive population
still has no fixed-polylogarithmic linear upper bound. This is a limitation of
range truncation, NOT a lower bound for signed energy or a disproof of Erdős 371. -/

namespace Erdos371ProductRangeGrowth

open Finset Filter Erdos371PrimeDiscrepancy Erdos371OffDiagonalEnergy
open Erdos371ProductSignTransport Erdos371ProductTransportFibers
open Erdos371ProductEnergyTransport Erdos371GcdCorrelation
open Erdos371PositiveCorrelationGrowth
open scoped Topology

/-- Ordered same-winner inputs whose transported index is at most `M`. -/
def shortPairs (M N : ℕ) : Finset (ℕ × ℕ) :=
  (allPairs N).filter fun nm => transport nm.1 nm.2 ≤ M

lemma shortPairs_card_eq (M N : ℕ) :
    (shortPairs M N).card = ∑ t ∈ range (M+1), (allFiber N t).card := by
  simpa only [shortPairs, allFiber, mem_range, Nat.lt_succ_iff] using
    (sum_card_fiberwise_eq_card_filter (allPairs N) (range (M+1))
      (fun nm => transport nm.1 nm.2)).symm

lemma shortPairs_card_le (M N : ℕ) :
    (shortPairs M N).card ≤ 4 * ∑ d ∈ Icc 1 (M+1), d.divisors.card := by
  rw [shortPairs_card_eq]
  calc
    _ ≤ ∑ t ∈ range (M+1), 2*(lower t).divisors.card :=
      sum_le_sum fun t _ => allFiber_card_le N t
    _ = 2 * ∑ t ∈ range (M+1), (lower t).divisors.card := by rw [mul_sum]
    _ ≤ 2 * (2 * ∑ d ∈ Icc 1 (M+1), d.divisors.card) :=
      Nat.mul_le_mul_left 2 (lower_divisor_sum_le (M+1))
    _ = _ := by ring

/-- The bound is independent of the input endpoint `N`. -/
theorem shortPairs_bound (M N : ℕ) :
    ((shortPairs M N).card : ℝ) ≤ 4*(M+1:ℕ)*(1+Real.log (M+1:ℕ)) := by
  have h : ((shortPairs M N).card : ℝ) ≤
      4 * ((∑ d ∈ Icc 1 (M+1), d.divisors.card : ℕ):ℝ) := by
    exact_mod_cast shortPairs_card_le M N
  nlinarith [divisor_sum_bound (M+1)]

/-- Each unordered positive pair is represented with its smaller input first. -/
def positivePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((range N).product (range N)).filter fun nm =>
    0 < nm.1 ∧ nm.1 < nm.2 ∧ winner nm.1 = winner nm.2 ∧ sign nm.1 = sign nm.2

lemma positivePairs_card (N : ℕ) : (positivePairs N).card = sameCount N := by
  simp only [positivePairs, card_eq_sum_ones, sum_filter, product_eq_sprod, sum_product]
  rw [sum_comm]
  unfold sameCount
  apply sum_congr rfl
  intro m hm
  rw [card_eq_sum_ones, sum_filter]
  have hsub : range m ⊆ range N := range_mono (mem_range.mp hm).le
  calc
    _ = ∑ n ∈ range m,
        if 0 < n ∧ n < m ∧ winner n=winner m ∧ sign n=sign m then 1 else 0 := by
      symm
      apply sum_subset hsub
      intro n hn hnm
      have hnm' : ¬n < m := by simpa only [mem_range] using hnm
      simp [hnm']
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      simp [mem_range.mp hn]

lemma positivePairs_subset (N : ℕ) : positivePairs N ⊆ allPairs N := by
  intro nm hnm
  obtain ⟨hr,hn,hnm,hw,hs⟩ := mem_filter.mp hnm
  have hn1 : 1 < nm.1 := by
    by_contra h
    have he : nm.1=1 := by omega
    have hw2 : winner nm.2=2 := by simpa [he,winner_one] using hw.symm
    have he2 := (winner_eq_two_iff nm.2).mp hw2
    omega
  exact mem_filter.mpr ⟨hr,hn1,by omega,hw⟩

/-- Positive pairs whose transported output lies beyond the specified range. -/
def longPositivePairs (M N : ℕ) : Finset (ℕ × ℕ) :=
  (positivePairs N).filter fun nm => M < transport nm.1 nm.2

lemma sameCount_le_short_add_long (M N : ℕ) :
    sameCount N ≤ (shortPairs M N).card + (longPositivePairs M N).card := by
  rw [← positivePairs_card]
  apply (card_le_card (show positivePairs N ⊆ shortPairs M N ∪ longPositivePairs M N from ?_)).trans
    (card_union_le _ _)
  intro nm hnm
  by_cases h : transport nm.1 nm.2 ≤ M
  · exact mem_union_left _ (mem_filter.mpr ⟨positivePairs_subset N hnm,h⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hnm,by omega⟩)

lemma short_linear_bound {C N : ℕ} (hN : C+1 ≤ N) (hlog : 1 ≤ Real.log (N:ℝ)) :
    ((shortPairs (C*N) N).card : ℝ) ≤ 12*(C+1:ℕ)*N*Real.log (N:ℝ) := by
  have hN1 : 1≤N := by omega
  have hM : C*N+1 ≤ (C+1)*N := by nlinarith
  have hMN : C*N+1 ≤ N^2 := by nlinarith
  have hl : Real.log (C*N+1:ℕ) ≤ 2*Real.log (N:ℝ) := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(C*N+1:ℕ))
      (show ((C*N+1:ℕ):ℝ) ≤ ((N^2:ℕ):ℝ) from Nat.cast_le.mpr hMN)
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using h
  have hMr : ((C*N+1:ℕ):ℝ) ≤ (C+1:ℕ)*(N:ℝ) := by exact_mod_cast hM
  have hL : 1+Real.log (C*N+1:ℕ) ≤ 3*Real.log (N:ℝ) := by linarith
  calc
    _ ≤ 4*(C*N+1:ℕ)*(1+Real.log (C*N+1:ℕ)) := shortPairs_bound _ _
    _ ≤ 4*((C+1:ℕ)*(N:ℝ))*(3*Real.log (N:ℝ)) := by
      gcongr
    _ = _ := by ring

/-- Removing all positive pairs whose transport stays below any fixed multiple
of `N` still leaves more than `N` times every fixed power of `log N` along some
arbitrarily large inputs. No assertion about their cancellation is made. -/
theorem not_eventually_polylog_longPositivePairs (C B : ℕ) (A : ℝ) :
    ¬ ∀ᶠ N : ℕ in atTop,
      ((longPositivePairs (C*N) N).card:ℝ) ≤ A*N*Real.log (N:ℝ)^B := by
  intro h
  apply not_eventually_polylog_sameCount (B+1) (12*(C+1:ℕ)+|A|)
  have hl : ∀ᶠ N : ℕ in atTop, 1≤Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1)
  filter_upwards [h,hl,eventually_ge_atTop (C+1)] with N hN hlN hCN
  have hs := short_linear_bound hCN hlN
  have hsum : (sameCount N:ℝ) ≤
      ((shortPairs (C*N) N).card:ℝ)+((longPositivePairs (C*N) N).card:ℝ) := by
    exact_mod_cast sameCount_le_short_add_long (C*N) N
  have hpB : 1≤Real.log (N:ℝ)^B := one_le_pow₀ hlN
  have hlog0 : 0≤Real.log (N:ℝ) := by linarith
  have hp0 : 0≤Real.log (N:ℝ)^B := by positivity
  have hpow : Real.log (N:ℝ)^B ≤ Real.log (N:ℝ)^(B+1) := by
    rw [pow_succ]
    nlinarith
  have hlogpow : Real.log (N:ℝ) ≤ Real.log (N:ℝ)^(B+1) := by
    rw [pow_succ]
    nlinarith
  have hA : A*N*Real.log (N:ℝ)^B ≤ |A| * N*Real.log (N:ℝ)^(B+1) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_abs_self A) (Nat.cast_nonneg N)
    · exact hpow
    · exact hp0
    · positivity
  have hs' : 12*(C+1:ℕ)*(N:ℝ)*Real.log (N:ℝ) ≤
      12*(C+1:ℕ)*(N:ℝ)*Real.log (N:ℝ)^(B+1) :=
    mul_le_mul_of_nonneg_left hlogpow (by positivity)
  nlinarith

end Erdos371ProductRangeGrowth

#print axioms Erdos371ProductRangeGrowth.shortPairs_bound
#print axioms Erdos371ProductRangeGrowth.not_eventually_polylog_longPositivePairs
