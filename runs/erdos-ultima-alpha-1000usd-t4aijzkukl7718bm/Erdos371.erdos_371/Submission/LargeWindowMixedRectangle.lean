import Submission.MixedRectangleCancellation
import Submission.RoughRadicalPowerBounds
import Submission.GrowingMixedRectangle

/-! The high-factor product window can extend to any fixed power strictly
below N. The remaining gap is not dismissed by letting the exponent vary. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem mixedRectangle_mean_error_of_radical (B D W X : ℕ → ℕ) (k L : ℕ) (hL : 0 < L)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hRad : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if roughRadical (B N) ((n+1)*(n+2)) ≤ D N*((B N)^k*X N) then (1 : ℝ) else 0)/N)
      atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
      (∑ n ∈ range N, |mixedComplementRectangleAt (B N) (D N) (W N) F (X N) (n+1)-
        highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1)|)/N < ε := by
  have hWP := subpower_below_power_cutoff B W L hL hB (hW.mono fun N h => h.2)
  have hthin := thin_subpower_band_zero B W k hBt hB hWP
  have hthin' : Tendsto (fun N : ℕ => (∑ n ∈ range N, if
      (activeBlockPrimes (largePrimeSet (B N) (W N)) (activePrimeAtoms (largePrimeSet (B N) (W N)) (n+1))).card ≤ k
      then (1 : ℝ) else 0)/N) atTop (𝓝 0) := by
    apply shifted_indicator_mean_zero (fun N n => (activeBlockPrimes (largePrimeSet (B N) (W N))
      (activePrimeAtoms (largePrimeSet (B N) (W N)) n)).card ≤ k)
    simpa only [sum_boole,thinPrimeBlockCount] using hthin
  have ht := short_band_exp_exception_zero B k
    (fun N n => (activeBlockPrimes (largePrimeSet (B N) (W N))
      (activePrimeAtoms (largePrimeSet (B N) (W N)) (n+1))).card ≤ k) hBt hthin'
  have hr := short_band_exp_exception_zero B k
    (fun N n => roughRadical (B N) ((n+1)*((n+1)+1)) ≤ D N*((B N)^k*X N)) (hBt) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hRad)
  have hbound := (ht.add hr).const_mul (2*(2 : ℝ)^(2*L))
  simp only [add_zero,mul_zero] at hbound
  intro ε hε
  filter_upwards [hBt.eventually_gt_atTop 1,hW,hWP 1,hWP k,hbound.eventually_lt_const hε]
    with N hb hw hbw hbk he
  simp only [pow_one] at hbw
  intro F hF
  have hs := sum_le_sum (s := range N) (fun n hn => mixedRectangle_point_error (B N) (D N) (W N) F
    (X N) k L N (n+1) hb hw.1 hw.2 hbw hbk (by omega) (by have := mem_range.mp hn; omega) hF)
  simp only [← mul_sum,sum_add_distrib] at hs
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N))
  convert he using 1; ring


theorem exists_large_window_mixed_rectangle (W X : ℕ → ℕ) (L q : ℕ) (hL : 0 < L) (hq : 2 ≤ q)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hX : ∀ᶠ N in atTop, (X N)^(2*q) ≤ N^(2*q-3)) :
    ∃ B H : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ (B N)^k,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,hweighted⟩ := exists_high_weighted_prefix_cutoffs W X L hW
  refine ⟨B,H,C,hBt,hHt,hB,hHB,hC,hbudget,hClim,?_⟩
  intro k ε hε
  have hsize : ∀ᶠ N in atTop, ((H N*N)*((B N)^k*X N))^(2*q) ≤ (N+1)^(2*(2*q-1)) := by
    filter_upwards [hHB,hX,subpower_pow_eventually_nat_le B hB ((k+1)*(2*q))] with N hh hx hb
    have hH : H N*(B N)^k ≤ (B N+1)^(k+1) := by
      calc
        _ ≤ (B N+1)*(B N+1)^k := Nat.mul_le_mul hh (Nat.pow_le_pow_left (Nat.le_succ _) k)
        _ = _ := by rw [pow_succ]; ring
    have hHp : (H N*(B N)^k)^(2*q) ≤ N := by
      rw [pow_mul] at hb
      exact (Nat.pow_le_pow_left hH (2*q)).trans hb
    have he : (H N*N)*((B N)^k*X N)=(H N*(B N)^k)*N*X N := by ring
    rw [he,mul_pow,mul_pow]
    calc
      _ ≤ N*N^(2*q)*N^(2*q-3) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hHp) hx
      _ = N^(2*(2*q-1)) := by rw [← pow_succ',← pow_add]; congr 1; omega
      _ ≤ (N+1)^(2*(2*q-1)) := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hr := roughRadical_small_power_proportion_zero B (fun N => (H N*N)*((B N)^k*X N))
    (2*q-1) hBt hB (by simpa only [show 2*q-1+1=2*q by omega] using hsize)
  have herr := mixedRectangle_mean_error_of_radical B (fun N => H N*N) W X k L hL hBt hB hW hr
  filter_upwards [herr (ε/2) (by positivity),hweighted k (ε/2) (by positivity),
    eventually_gt_atTop (0 : ℕ)] with N he hw hN
  intro F hF
  have hdiff : |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N-
      (∑ n ∈ range N, highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N| < ε/2 := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)).trans_lt (he F hF)
  have htri := abs_sub_le
    ((∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N)
    ((∑ n ∈ range N, highDivisorWeight (W N) (X N) (n+1)*untruncatedComplementPrefix (B N) F (n+1))/N) 0
  simp only [sub_zero] at htri
  linarith [hw F hF]



theorem exists_cancelled_growing_large_rectangle (W X : ℕ → ℕ) (L q : ℕ) (hL : 0 < L) (hq : 2 ≤ q)
    (hW : ∀ᶠ N in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hX : ∀ᶠ N in atTop, (X N)^(2*q) ≤ N^(2*q-3)) :
    ∃ B H U : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto U atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) ∧ (∀ᶠ N in atTop, U N ≤ W N) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ F ≤ U N,
        |(∑ n ∈ range N, mixedComplementRectangleAt (B N) (H N*N) (W N) F (X N) (n+1))/N| < ε) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hbudget,hClim,hfixed⟩ := exists_large_window_mixed_rectangle W X L q hL hq hW hX
  obtain ⟨K,hK,hlogU,hmax⟩ := exists_growing_rectangle_window B H W X hB hlog hfixed
  let U : ℕ → ℕ := fun N => (B N)^(K N)
  have hU : Tendsto U atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hB.eventually_ge_atTop M,hB.eventually_gt_atTop 0,hK.eventually_ge_atTop 1]
      with N hb hb0 hk
    exact hb.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hb0 hk)
  have hUl : Tendsto (fun N => Real.log (U N+1 : ℝ)/Real.log N) atTop (𝓝 0) := by
    simpa only [U,Nat.cast_pow] using hlogU
  refine ⟨B,H,U,C,hB,hH,hU,hlog,hUl,hHB,hC,hbudget,hClim,?_,?_,hmax⟩
  · intro k
    filter_upwards [hB.eventually_gt_atTop 0,hK.eventually_ge_atTop k] with N hb hk
    exact Nat.pow_le_pow_right hb hk
  · simpa only [pow_one] using subpower_below_power_cutoff U W L hL hUl (hW.mono fun N h => h.2) 1


#print axioms exists_large_window_mixed_rectangle
#print axioms exists_cancelled_growing_large_rectangle
end Erdos371
