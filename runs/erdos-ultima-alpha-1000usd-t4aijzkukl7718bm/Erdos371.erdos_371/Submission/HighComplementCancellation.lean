import Submission.HighComplementAlgebra
import Submission.SubpowerOccupiedBand

/-! Signed cancellation for complementary divisors supported entirely above a
fixed-power threshold, in a safe product window. The chosen B,H retain the
small-divisor prefix budget. This does not cover mixed low/high divisors. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma highComplementAt_error_bound (B D W X L N n : ℕ) (hBW : B ≤ W)
    (hW : 1 < W) (hWN : N+1 ≤ W^L) (hnN : n ≤ N) :
    |highComplementAt B D W X n-highDivisorWeight W X n*untruncatedRoughUnit B n| ≤
      2*(2 : ℝ)^(2*L)*
        ((if activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)=∅ then 1 else 0)+
          (if roughRadical B (n*(n+1)) ≤ D*X then 1 else 0)) := by
  by_cases hn : n=0
  · subst n
    rw [highComplementAt_zero,highDivisorWeight_zero,zero_mul,sub_self,abs_zero]
    positivity
  have hn0 : 0 < n := by omega
  have hb := high_weight_and_complement_bound W L N n B D X hW hWN hn0 hnN
  have hbound : |highComplementAt B D W X n-highDivisorWeight W X n*untruncatedRoughUnit B n| ≤
      2*(2 : ℝ)^(2*L) := by
    have hh := abs_sub (highComplementAt B D W X n) (highDivisorWeight W X n*untruncatedRoughUnit B n)
    rw [abs_mul,untruncatedRoughUnit_abs,mul_one] at hh
    linarith
  by_cases he : activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)=∅
  · rw [if_pos he]
    exact hbound.trans (by split_ifs <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2*L)])
  · rw [if_neg he,zero_add]
    by_cases hr : roughRadical B (n*(n+1)) ≤ D*X
    · rw [if_pos hr,mul_one]
      exact hbound
    · rw [if_neg hr,mul_zero]
      obtain ⟨q,hq⟩ := nonempty_iff_ne_empty.mpr he
      rw [rough_active_block_eq B W n hn0] at hq
      obtain ⟨hqr,hqW⟩ := mem_filter.mp hq
      have hR : 1 < roughRadical B (n*(n+1)) := Nat.nonempty_primeFactors.mp ⟨q,hqr⟩
      have hm : (roughRadical B (n*(n+1))).minFac ≤ W :=
        (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hqr).two_le (Nat.dvd_of_mem_primeFactors hqr)).trans hqW
      rw [highComplementAt_eq_weighted_unit B D W X n hBW hR hm (by omega),sub_self,abs_zero]

lemma highComplementAt_mean_absolute_error_zero (B D W X : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hsize : ∀ᶠ N in atTop, (D N*X N)^2 ≤ (N+1)^3) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      |highComplementAt (B N) (D N) (W N) (X N) n-
        highDivisorWeight (W N) (X N) n*untruncatedRoughUnit (B N) n|)/N) atTop (𝓝 0) := by
  have hWP := subpower_below_power_cutoff B W L hL hB (hW.mono fun N h => h.2)
  have he := empty_subpower_band_zero B W hBt hB hWP
  have hr := rough_radical_small_proportion_zero B (fun N => D N*X N) hBt hB hsize
  have ht := (he.add hr).const_mul (2*(2 : ℝ)^(2*L))
  simp only [add_zero,mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg
    (sum_nonneg fun n _ => abs_nonneg _) (Nat.cast_nonneg N)) _ ht
  filter_upwards [hW,hWP 1] with N hw hbw
  simp only [pow_one] at hbw
  have hs := sum_le_sum (s := range N) (fun n hn =>
    highComplementAt_error_bound (B N) (D N) (W N) (X N) L N n hbw hw.1 hw.2 (mem_range.mp hn).le)
  have hcount : (∑ n ∈ range N, if activeBlockPrimes (largePrimeSet (B N) (W N))
      (activePrimeAtoms (largePrimeSet (B N) (W N)) n)=∅ then (1 : ℝ) else 0)=
      (emptyPrimeBlockCount (largePrimeSet (B N) (W N)) N : ℝ) := by
    simp only [sum_boole,emptyPrimeBlockCount]
  simp only [← mul_sum,sum_add_distrib,hcount] at hs
  convert div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N) using 1; ring

/-- This estimates actual nonunit complementary indices e whose every prime
factor exceeds W(N) and whose product is at most X(N). It is not a statement
about all indices with just their LARGEST prime above W(N). -/
theorem exists_high_complement_cancellation (W X : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hX : ∀ᶠ N in atTop, (X N)^4 ≤ N) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ =>
        (∑ n ∈ range N, highComplementAt (B N) (H N*N) (W N) (X N) n)/N)
        atTop (𝓝 0) := by
  classical
  let A : ℝ := 2^(2*L)
  have hA : 0 < A := by dsimp [A]; positivity
  let w : ℕ → ℕ → ℝ := fun N n =>
    if 1 < W N ∧ N+1 ≤ (W N)^L then highDivisorWeight (W N) (X N) n/A else 0
  have hw : ∀ N n, n < N → |w N n| ≤ 1 := by
    intro N n hn
    dsimp [w]
    split_ifs with hg
    · by_cases hn0 : n=0
      · subst n
        rw [highDivisorWeight_zero,zero_div,abs_zero]
        norm_num
      · rw [abs_div,abs_of_pos hA]
        apply (div_le_one hA).mpr
        exact (high_weight_and_complement_bound (W N) L N n 0 0 (X N) hg.1 hg.2 (by omega) hn.le).1
    · norm_num
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hunit⟩ := exists_weighted_unit_subpower_prefix_budget w hw
  have hweighted : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, highDivisorWeight (W N) (X N) n*untruncatedRoughUnit (B N) n)/N)
      atTop (𝓝 0) := by
    have hh := hunit.const_mul A
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hW] with N hwN
    dsimp only [w]
    simp only [if_pos hwN,← mul_div_assoc,mul_sum]
    congr 1
    apply sum_congr rfl
    intro n _
    field_simp
  have hsize : ∀ᶠ N in atTop, ((H N*N)*X N)^2 ≤ (N+1)^3 := by
    filter_upwards [hHB,hX,subpower_pow_eventually_nat_le B hB 4] with N hh hx hb
    have hH4 : (H N)^4 ≤ N := (Nat.pow_le_pow_left hh 4).trans hb
    have hp : ((H N)^2*(X N)^2)^2 ≤ N^2 := by nlinarith [Nat.mul_le_mul hH4 hx]
    have hp' : (H N)^2*(X N)^2 ≤ N := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hp
    have hh := Nat.mul_le_mul_right (N^2) hp'
    nlinarith
  have herr := highComplementAt_mean_absolute_error_zero B (fun N => H N*N) W X L hL hBt hB hW hsize
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, highComplementAt (B N) (H N*N) (W N) (X N) n)/N-
      (∑ n ∈ range N, highDivisorWeight (W N) (X N) n*untruncatedRoughUnit (B N) n)/N)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herr
    apply Eventually.of_forall
    intro N
    rw [Real.norm_eq_abs,← sub_div,← sum_sub_distrib,abs_div,
      abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_⟩
  simpa only [sub_add_cancel,add_zero] using hd.add hweighted

#print axioms highComplementAt_mean_absolute_error_zero
#print axioms exists_high_complement_cancellation
end Erdos371
