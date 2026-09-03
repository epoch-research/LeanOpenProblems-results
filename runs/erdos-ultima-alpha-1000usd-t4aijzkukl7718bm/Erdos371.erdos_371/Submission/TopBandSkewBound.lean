import Submission.UpperHalfSmoothSkew
import Submission.BothLargePrimeBound

/-! A uniform quadratic upper bound for the top corner of the signed
smooth-cutoff kernel. This controls a boundary range, not the interior
positive-power cutoffs required for the density conjecture. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

noncomputable def shiftedLargePairSet (B N : ℕ) : Finset ℕ :=
  (range N).filter fun n => B < Nat.maxPrimeFac (n+1) ∧ B < Nat.maxPrimeFac (n+2)

lemma smooth_band_skew_term_abs_le (B C n : ℕ) (hBC : B ≤ C) :
    |(smoothIndicator B (n+1)-smoothIndicator C (n+1))*(smoothIndicator C (n+2)-1)-
      (smoothIndicator C (n+1)-1)*(smoothIndicator B (n+2)-smoothIndicator C (n+2))| ≤
        if B < Nat.maxPrimeFac (n+1) ∧ B < Nat.maxPrimeFac (n+2) then 1 else 0 := by
  unfold smoothIndicator
  split_ifs <;> norm_num <;> omega

lemma band_kernel_abs_le_large_pairs (B C N : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C) :
    |divisorSkewKernel (primeBandMoebius B C) (properRoughMoebius C) N| ≤
      (shiftedLargePairSet B N).card := by
  rw [← divisorConvolution_skew_prefix]
  calc
    _ ≤ ∑ n ∈ range N,
        |divisorConvolution (primeBandMoebius B C) (n+1)*divisorConvolution (properRoughMoebius C) (n+2)-
          divisorConvolution (properRoughMoebius C) (n+1)*divisorConvolution (primeBandMoebius B C) (n+2)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N,
        if B < Nat.maxPrimeFac (n+1) ∧ B < Nat.maxPrimeFac (n+2) then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      rw [primeBandMoebius_convolution B C (n+1) hB hBC (by omega),
        primeBandMoebius_convolution B C (n+2) hB hBC (by omega),
        properRoughMoebius_convolution C (n+1) (hB.trans hBC) (by omega),
        properRoughMoebius_convolution C (n+2) (hB.trans hBC) (by omega)]
      exact smooth_band_skew_term_abs_le B C n hBC
    _ = _ := by simp [shiftedLargePairSet]

lemma shiftedLargePairSet_card_bound (B N : ℕ) (u : ℝ) (hcut : (N : ℝ)^(1-u) ≤ B) :
    (shiftedLargePairSet B N).card ≤ (bothLargePrimeSet N u).card+1 := by
  classical
  have hs : (shiftedLargePairSet B N).card ≤ (bothLargePrimeSet N u ∪ {N}).card := by
    apply card_le_card_of_injOn (fun n => n+1)
    · intro n hn
      simp only [mem_coe] at hn ⊢
      obtain ⟨hnN,hp,hq⟩ := mem_filter.mp hn
      have hnN' := mem_range.mp hnN
      by_cases hnlt : n+1 < N
      · apply mem_union_left
        apply mem_filter.mpr
        refine ⟨mem_range.mpr hnlt,?_,?_⟩
        · exact hcut.trans_lt (by exact_mod_cast hp)
        · exact hcut.trans_lt (by exact_mod_cast hq)
      · apply mem_union_right
        simp only [mem_singleton]
        omega
    · intro n hn m hm he
      dsimp at he
      omega
  exact hs.trans (by simpa using card_union_le (bothLargePrimeSet N u) {N})

/-- An absolute bound for the already-summed signed kernel. The estimate
is uniform in the upper cutoff C. -/
lemma band_kernel_top_ratio_bound (B C N : ℕ) (u : ℝ) (hB : 1 ≤ B) (hBC : B ≤ C)
    (hN : 1 < N) (hu0 : 0 ≤ u) (hu : u ≤ 1/8) (hcut : (N : ℝ)^(1-u) ≤ B) :
    |divisorSkewKernel (primeBandMoebius B C) (properRoughMoebius C) N|/N ≤
      largePairConstant*(u+1/Real.log N)^2+(2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ)+1/N := by
  have hcard := (Nat.cast_le (α := ℝ)).mpr (shiftedLargePairSet_card_bound B N u hcut)
  push_cast at hcard
  have hb := div_le_div_of_nonneg_right ((band_kernel_abs_le_large_pairs B C N hB hBC).trans hcard)
    (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hb
  exact hb.trans (add_le_add (bothLargePrimeSet_ratio_bound N u hN hu0 hu) le_rfl)

/-- Near the exponent-one boundary the signed band kernel has upper
absolute proportion O(u^2). For fixed u>0 this is not an o(1) estimate. -/
theorem band_kernel_top_eventually_le (B C : ℕ → ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/8)
    (hcut : ∀ᶠ N : ℕ in atTop, 1 ≤ B N ∧ B N ≤ C N ∧ (N : ℝ)^(1-u) ≤ B N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |divisorSkewKernel (primeBandMoebius (B N) (C N)) (properRoughMoebius (C N)) N|/N ≤
        largePairConstant*u^2+ε := by
  have ht := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  filter_upwards [hcut,bothLargePrimeSet_eventually_ratio_le u hu0 hu (ε/2) (by positivity),
    ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with N hc hp ht
  have hcard := (Nat.cast_le (α := ℝ)).mpr (shiftedLargePairSet_card_bound (B N) N u hc.2.2)
  push_cast at hcard
  have hb := div_le_div_of_nonneg_right ((band_kernel_abs_le_large_pairs (B N) (C N) N hc.1 hc.2.1).trans hcard)
    (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hb
  linarith

/-- The same bound applies to the unweighted prime-band discrepancy when
the cutoffs lie above the square-root threshold. -/
theorem primeBandDiscrepancy_top_eventually_le (B C : ℕ → ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1/8)
    (hcut : ∀ᶠ N : ℕ in atTop, 1 ≤ B N ∧ B N ≤ C N ∧ (N : ℝ)^(1-u) ≤ B N)
    (hsize : ∀ᶠ N : ℕ in atTop, N+1 ≤ (B N)^2) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |primeBandDiscrepancy (B N) (C N) N|/N ≤ largePairConstant*u^2+ε := by
  filter_upwards [band_kernel_top_eventually_le B C u hu0 hu hcut ε hε,hcut,hsize] with N hb hc hs
  rwa [divisorSkewKernel_above_sqrt (B N) (C N) N hc.2.1 hs] at hb

#print axioms band_kernel_top_eventually_le
#print axioms primeBandDiscrepancy_top_eventually_le
end Erdos371
