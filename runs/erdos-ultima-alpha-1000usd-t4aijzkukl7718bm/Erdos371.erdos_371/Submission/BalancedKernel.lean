import Submission.RoughPartGoodPairs

/-! The exact reciprocal-discrepancy kernel for the truncated rectangle. -/

namespace Erdos371

noncomputable def rectangularWeight (B D K N a b : ℕ) : ℝ :=
  if K * a ≤ N ∧ K * b ≤ N then roughBilinearWeight B D a b else 0

lemma rectangularWeight_swap (B D K N a b : ℕ) :
    rectangularWeight B D K N b a = -rectangularWeight B D K N a b := by
  unfold rectangularWeight
  rw [roughBilinearWeight_swap B D a b]
  by_cases ha : K * a ≤ N <;> by_cases hb : K * b ≤ N <;> simp [ha, hb]

lemma balancedBilinearSum_eq_rectangularWeight (B D K N n : ℕ) :
    balancedBilinearSum B D K N n =
      ∑ a ∈ n.divisors, ∑ b ∈ (n + 1).divisors, rectangularWeight B D K N a b := by
  unfold balancedBilinearSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hKa : K * a ≤ N
  · simp [rectangularWeight, hKa, Finset.sum_filter]
  · simp [rectangularWeight, hKa]

lemma balancedBilinearSum_range (B D K N n : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    balancedBilinearSum B D K N n =
      ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        if a ∣ n ∧ b ∣ n + 1 then rectangularWeight B D K N a b else 0 := by
  rw [balancedBilinearSum_eq_rectangularWeight,
    sum_divisors_eq_range n (N + 2) hn (by omega)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_divisors_eq_range (n + 1) (N + 2) (by omega) (by omega)]
  by_cases h : a ∣ n <;> simp [h]

lemma balancedBilinearSum_prefix_kernel (B D K N : ℕ) :
    (∑ n ∈ Finset.range N, balancedBilinearSum B D K N (n + 1)) =
      ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        rectangularWeight B D K N a b * (bilinearCount N a b : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.range N, ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        if a ∣ n + 1 ∧ b ∣ n + 2 then rectangularWeight B D K N a b else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact balancedBilinearSum_range B D K N (n + 1) (by omega) (Finset.mem_range.mp hn)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_filter]
      simp [bilinearCount, mul_comm]

lemma balancedBilinearSum_prefix_discrepancy (B D K N : ℕ) :
    2 * (∑ n ∈ Finset.range N, balancedBilinearSum B D K N (n + 1)) =
      ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        rectangularWeight B D K N a b * ((bilinearCount N a b : ℝ) - bilinearCount N b a) := by
  rw [balancedBilinearSum_prefix_kernel]
  have he :
      (∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        rectangularWeight B D K N a b * (bilinearCount N b a : ℝ)) =
      -(∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        rectangularWeight B D K N a b * (bilinearCount N a b : ℝ)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [rectangularWeight_swap B D K N a b, neg_mul]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [he]
  ring

open Filter in
/-- Exact normalized kernel form of the structured-cutoff reduction.
Its convergence to zero remains the unproved step. -/
theorem density_iff_quantile_discrepancy_kernel (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        (∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
          rectangularWeight (B N) (nearLinearCutoff N) (harmonicCofactorCutoff (B N)) N a b *
            ((bilinearCount N a b : ℝ) - bilinearCount N b a)) / (2 * N))
          atTop (nhds 0)) := by
  rw [density_iff_quantile_balanced B hBatTop hB]
  have he (N : ℕ) :
      (∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
        rectangularWeight (B N) (nearLinearCutoff N) (harmonicCofactorCutoff (B N)) N a b *
          ((bilinearCount N a b : ℝ) - bilinearCount N b a)) / (2 * N) =
        (∑ n ∈ Finset.range N, balancedBilinearSum (B N) (nearLinearCutoff N)
          (harmonicCofactorCutoff (B N)) N (n + 1)) / N := by
    rw [← balancedBilinearSum_prefix_discrepancy]
    ring
  simp_rw [he]

noncomputable def rectangularAbsoluteMass (B D K N : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N + 2), ∑ b ∈ Finset.range (N + 2),
    ‖rectangularWeight B D K N a b * ((bilinearCount N a b : ℝ) - bilinearCount N b a)‖

lemma bilinearCount_large_product_discrepancy (N n a b : ℕ) (hn : n < N)
    (ha : a ∣ n + 1) (hb : b ∣ n + 2) (hab : 2 * N + 1 < a * b) :
    (bilinearCount N a b : ℝ) - bilinearCount N b a = 1 := by
  have hc := divisor_pair_coprime (n + 1) a b ha hb
  have hforward : bilinearCount N a b = 1 := by
    apply le_antisymm (bilinearCount_le_one N a b hc (by omega))
    apply Nat.succ_le_iff.mpr
    exact Finset.card_pos.mpr ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, ha, hb⟩⟩
  have hreverse : bilinearCount N b a = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨hmN, hbm, ham⟩ := Finset.mem_filter.mp hm
    have hleft : a ∣ n + m + 3 := by convert Nat.dvd_add ha ham using 1 <;> omega
    have hright : b ∣ n + m + 3 := by convert Nat.dvd_add hb hbm using 1 <;> omega
    have hmul := hc.mul_dvd_of_dvd_of_dvd hleft hright
    have hle := Nat.le_of_dvd (by omega : 0 < n + m + 3) hmul
    have hmN' := Finset.mem_range.mp hmN
    omega
  simp [hforward, hreverse]

lemma roughBilinearWeight_norm_eq_one (B D a b : ℕ)
    (ha : 1 < a) (hb : 1 < b) (hD : D < a * b)
    (haB : B < a.minFac) (hbB : B < b.minFac)
    (hsa : Squarefree a) (hsb : Squarefree b) (hc : a.Coprime b) :
    ‖roughBilinearWeight B D a b‖ = 1 := by
  have hμ (m : ℕ) (hm : Squarefree m) : ‖(ArithmeticFunction.moebius m : ℝ)‖ = 1 := by
    rw [Real.norm_eq_abs, ← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hm]
    norm_num
  have hs : ‖bilinearSign a b‖ = 1 := by
    have hne := coprime_minFac_ne a b ha hc
    rcases lt_or_gt_of_ne hne with h | h <;> simp [bilinearSign, h, h.not_gt]
  rw [roughBilinearWeight, if_pos ⟨ha, hb, hD, haB, hbB⟩, norm_mul, norm_mul,
    hμ a hsa, hμ b hsb, hs]
  norm_num

#print axioms balancedBilinearSum_prefix_discrepancy
#print axioms density_iff_quantile_discrepancy_kernel
#print axioms bilinearCount_large_product_discrepancy
#print axioms roughBilinearWeight_norm_eq_one
end Erdos371
