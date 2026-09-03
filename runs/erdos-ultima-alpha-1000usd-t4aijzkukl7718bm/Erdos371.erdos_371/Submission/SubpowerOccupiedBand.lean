import Submission.SubpowerPolynomialCutoff

/-! A subpower lower cutoff and a fixed-power (or larger) upper cutoff leave
an occupied prime band on density one. These are coverage estimates only. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma emptyPrimeBlockCount_antitone (P Q : Finset ℕ) (hPQ : P ⊆ Q) (N : ℕ) :
    emptyPrimeBlockCount Q N ≤ emptyPrimeBlockCount P N := by
  apply card_le_card
  intro n hn
  obtain ⟨hn,hQ⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hn,?_⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hloc := activeBlockPrimes_congr P (activePrimeAtoms P n) (activePrimeAtoms Q n)
    (activePrimeAtoms_locality P Q hPQ n)
  rw [hloc] at hp
  have h := activeBlockPrimes_mono P Q hPQ (activePrimeAtoms Q n) hp
  rw [hQ] at h
  exact notMem_empty p h

lemma subpower_below_power_cutoff (B W : ℕ → ℕ) (L : ℕ) (hL : 0 < L)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hW : ∀ᶠ N in atTop, N+1 ≤ (W N)^L) (k : ℕ) :
    ∀ᶠ N in atTop, (B N)^k ≤ W N := by
  filter_upwards [hW,subpower_pow_eventually_nat_le B hB (k*L)] with N hw hb
  have hp : ((B N)^k)^L ≤ (W N)^L := by
    rw [← pow_mul]
    exact ((Nat.pow_le_pow_left (Nat.le_succ (B N)) (k*L)).trans hb).trans (by omega)
  exact (Nat.pow_le_pow_iff_left (by omega : L ≠ 0)).mp hp

lemma empty_subpower_band_zero (B W : ℕ → ℕ)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hW : ∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ W N) :
    Tendsto (fun N : ℕ => (emptyPrimeBlockCount (largePrimeSet (B N) (W N)) N : ℝ)/N)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨J,hJ,hJs⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((tendsto_const_div_atTop_nhds_zero_nat (16 : ℝ)).eventually_lt_const
      (show (0 : ℝ) < ε/2 by positivity))).exists
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hBt)).eventually_ge_atTop
    (2*(1+primePowerErrorConstant+Real.log 4))
  have htail : Tendsto (fun N : ℕ => 32*((B N : ℝ)^(2^J)+1)/(N*J)) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => (B N : ℝ)^(2^J)/N) atTop (𝓝 0) := by
      apply squeeze_zero (fun N => by positivity) _ (subpower_pow_div_tendsto_zero B hB (2^J))
      intro N
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
    have hh := (hb.add tendsto_one_div_atTop_nhds_zero_nat).const_mul (32/(J : ℝ))
    simp only [add_zero,mul_zero] at hh
    convert hh using 1
    funext N
    ring
  filter_upwards [hBt.eventually_gt_atTop 1,hlog,hW (2^J),
    htail.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hb hl hw ht hN
  have hs := iteratedPrimeBlock_empty_bound (B N) J 1 0 N hb hJ hN (by omega) hl
  have hsub : iteratedPrimeBlock (B N) J 0 ⊆ largePrimeSet (B N) (W N) := by
    intro p hp
    obtain ⟨hpp,hpl,hpu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
    simp only [blockCutoff,Nat.zero_add,Nat.mul_zero,pow_zero,pow_one,Nat.mul_one] at hpl hpu
    exact (mem_largePrimeSet_iff p _ _).mpr ⟨hpp,hpl,hpu.trans hw⟩
  have hc : (emptyPrimeBlockCount (largePrimeSet (B N) (W N)) N : ℝ)/N ≤
      (emptyPrimeBlockCount (iteratedPrimeBlock (B N) J 0) N : ℝ)/N := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast emptyPrimeBlockCount_antitone _ _ hsub N
  simp only [blockCutoff,Nat.mul_one,Nat.cast_pow] at hs
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))]
  exact hc.trans_lt (hs.trans_lt (by linarith))

lemma rough_radical_small_proportion_zero (B D : ℕ → ℕ)
    (hBt : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hD : ∀ᶠ N in atTop, (D N)^2 ≤ (N+1)^3) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, if roughRadical (B N) (n*(n+1)) ≤ D N then (1 : ℝ) else 0)/N)
      atTop (𝓝 0) := by
  have hunit := roughComplementUnit_absolute_average_one_of_sq B D hBt hB hD
  have hshift : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, if roughRadical (B N) ((n+1)*(n+2)) ≤ D N then (1 : ℝ) else 0)/N)
      atTop (𝓝 0) := by
    have hh := hunit.const_sub (1 : ℝ)
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have he (n : ℕ) : (if roughRadical (B N) ((n+1)*(n+2)) ≤ D N then (1 : ℝ) else 0)=
        1-‖roughComplementUnit (B N) (D N) (n+1)‖ := by
      rw [roughComplementUnit_norm]
      simp only [Nat.add_assoc,Nat.reduceAdd]
      split_ifs <;> norm_num at * <;> omega
    simp only [he,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,sub_div,div_self hNr]
  have ht := hshift.add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => div_nonneg (sum_nonneg fun n _ => by split_ifs <;> norm_num) (Nat.cast_nonneg N)) _ ht
  intro N
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  let f : ℕ → ℝ := fun n => if roughRadical (B N) (n*(n+1)) ≤ D N then 1 else 0
  have hs := sum_range_succ' f N
  rw [sum_range_succ] at hs
  have h0 : f 0 ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
  have hN : 0 ≤ f N := by dsimp [f]; split_ifs <;> norm_num
  change (∑ n ∈ range N, f n) ≤ (∑ n ∈ range N, f (n+1))+1
  linarith

#print axioms empty_subpower_band_zero
#print axioms rough_radical_small_proportion_zero
end Erdos371
