import Submission.BalancedKernel

/-! The actual truncated reciprocal-discrepancy kernel has at least linear
absolute mass. This rules out proving its required zero mean by taking the
absolute value of every summand. It is not a disproof of the conjecture. -/

namespace Erdos371

lemma goodRoughPair_product_large (B K N n : ℕ) (hN : 2 ≤ N)
    (hn : n ∈ goodRoughPairSet B K N) :
    2 * N + 1 < roughPrimePart B (n + 1) * roughPrimePart B (n + 2) := by
  obtain ⟨hnN, h1, h2⟩ := Finset.mem_filter.mp hn
  have hnN' := Finset.mem_range.mp hnN
  have ha := good_rough_part_data B K N (n + 1) hN (by omega) (by omega) h1
  have hb := good_rough_part_data B K N (n + 2) hN (by omega) (by omega) h2
  rcases le_total (roughPrimePart B (n + 1)) (roughPrimePart B (n + 2)) with h | h
  · nlinarith [Nat.mul_le_mul_left (roughPrimePart B (n + 1)) h]
  · nlinarith [Nat.mul_le_mul_left (roughPrimePart B (n + 2)) h]

lemma goodRoughPair_kernel_term (B D K N n : ℕ) (hN : 2 ≤ N) (hD : D ≤ N)
    (hn : n ∈ goodRoughPairSet B K N) :
    ‖rectangularWeight B D K N (roughPrimePart B (n + 1)) (roughPrimePart B (n + 2)) *
      ((bilinearCount N (roughPrimePart B (n + 1)) (roughPrimePart B (n + 2)) : ℝ) -
        bilinearCount N (roughPrimePart B (n + 2)) (roughPrimePart B (n + 1)))‖ = 1 := by
  have hprod := goodRoughPair_product_large B K N n hN hn
  obtain ⟨hnN, h1, h2⟩ := Finset.mem_filter.mp hn
  have hnN' := Finset.mem_range.mp hnN
  obtain ⟨ha1, hsa, haB, hKa, _⟩ := good_rough_part_data B K N (n + 1) hN (by omega) (by omega) h1
  obtain ⟨hb1, hsb, hbB, hKb, _⟩ := good_rough_part_data B K N (n + 2) hN (by omega) (by omega) h2
  have hda := roughPrimePart_dvd B (n + 1) (by omega)
  have hdb := roughPrimePart_dvd B (n + 2) (by omega)
  rw [bilinearCount_large_product_discrepancy N n _ _ hnN' hda hdb hprod,
    mul_one, rectangularWeight, if_pos ⟨hKa, hKb⟩]
  exact roughBilinearWeight_norm_eq_one B D _ _ ha1 hb1 (by omega) haB hbB hsa hsb
    (divisor_pair_coprime (n + 1) _ _ hda hdb)

lemma goodRoughPair_map_injective (B K N : ℕ) (hN : 2 ≤ N) :
    Set.InjOn (fun n => (roughPrimePart B (n + 1), roughPrimePart B (n + 2)))
      (goodRoughPairSet B K N : Set ℕ) := by
  intro n hn m hm he
  simp only [Finset.mem_coe] at hn hm
  have hprod := goodRoughPair_product_large B K N n hN hn
  have hnN := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hmN := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have he1 : roughPrimePart B (n + 1) = roughPrimePart B (m + 1) := congrArg Prod.fst he
  have he2 : roughPrimePart B (n + 2) = roughPrimePart B (m + 2) := congrArg Prod.snd he
  have hna := roughPrimePart_dvd B (n + 1) (by omega)
  have hnb := roughPrimePart_dvd B (n + 2) (by omega)
  have hma : roughPrimePart B (n + 1) ∣ m + 1 := by rw [he1]; exact roughPrimePart_dvd B (m + 1) (by omega)
  have hmb : roughPrimePart B (n + 2) ∣ m + 2 := by rw [he2]; exact roughPrimePart_dvd B (m + 2) (by omega)
  have hc := divisor_pair_coprime (n + 1) _ _ hna hnb
  exact (Finset.card_le_one.mp (bilinearCount_le_one N _ _ hc (by omega))) n
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, hna, hnb⟩) m
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmN, hma, hmb⟩)

/-- Each good consecutive pair supplies a distinct absolute-value-one entry
of the actual discrepancy matrix, even with the near-linear product cutoff. -/
theorem rectangularAbsoluteMass_lower (B D K N : ℕ) (hN : 2 ≤ N) (hD : D ≤ N) :
    ((goodRoughPairSet B K N).card : ℝ) ≤ rectangularAbsoluteMass B D K N := by
  classical
  let G := goodRoughPairSet B K N
  let f : ℕ → ℕ × ℕ := fun n => (roughPrimePart B (n + 1), roughPrimePart B (n + 2))
  let R := Finset.range (N + 2) ×ˢ Finset.range (N + 2)
  let w : ℕ × ℕ → ℝ := fun ab => ‖rectangularWeight B D K N ab.1 ab.2 *
    ((bilinearCount N ab.1 ab.2 : ℝ) - bilinearCount N ab.2 ab.1)‖
  have hf : Set.InjOn f (G : Set ℕ) := goodRoughPair_map_injective B K N hN
  have hmem : G.image f ⊆ R := by
    intro ab hab
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hab
    have hnN := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hle := Nat.le_of_dvd (by omega : 0 < n + 1) (roughPrimePart_dvd B (n + 1) (by omega))
      dsimp only [f]
      omega
    · apply Finset.mem_range.mpr
      have hle := Nat.le_of_dvd (by omega : 0 < n + 2) (roughPrimePart_dvd B (n + 2) (by omega))
      dsimp only [f]
      omega
  calc
    _ = ∑ n ∈ G, w (f n) := by
      have he : ∀ n ∈ G, w (f n) = 1 := fun n hn => goodRoughPair_kernel_term B D K N n hN hD hn
      rw [Finset.sum_congr rfl he]
      simp [G]
    _ = ∑ ab ∈ G.image f, w ab := (Finset.sum_image hf).symm
    _ ≤ ∑ ab ∈ R, w ab :=
      Finset.sum_le_sum_of_subset_of_nonneg hmem (fun ab _ _ => norm_nonneg _)
    _ = _ := by rw [Finset.sum_product]; rfl

open Filter in
/-- For every growing subpower rough cutoff, the normalized absolute mass
is eventually at least 1-epsilon. This includes the concrete cutoffs in the
strongest reduction of the conjecture. -/
theorem rectangularAbsoluteMass_eventually_lower (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, 1 - ε ≤
      rectangularAbsoluteMass (B N) (nearLinearCutoff N) (harmonicCofactorCutoff (B N)) N / N := by
  have ht := goodRoughPairSet_quantile_density_one B hBatTop hB
  filter_upwards [(tendsto_order.mp ht).1 (1 - ε) (by linarith), eventually_ge_atTop 2] with N hNg hN
  exact hNg.le.trans (div_le_div_of_nonneg_right
    (rectangularAbsoluteMass_lower (B N) (nearLinearCutoff N) (harmonicCofactorCutoff (B N)) N hN
      (nearLinearCutoff_le_self N)) (Nat.cast_nonneg N))

open Filter in
/-- A direct triangle-inequality proof of the remaining o(N) cancellation
cannot work: the sum of the absolute values does not tend to zero. -/
theorem rectangularAbsoluteMass_not_tendsto_zero :
    ¬Tendsto (fun N : ℕ =>
      rectangularAbsoluteMass (subpowerCutoff N) (nearLinearCutoff N)
        (harmonicCofactorCutoff (subpowerCutoff N)) N / N) atTop (nhds 0) := by
  intro h
  have hl := rectangularAbsoluteMass_eventually_lower subpowerCutoff subpowerCutoff_atTop
    subpowerCutoff_log_ratio_tendsto_zero (1 / 2) (by norm_num)
  have hu := (tendsto_order.mp h).2 (1 / 2) (by norm_num)
  obtain ⟨N, hN, hN'⟩ := (hl.and hu).exists
  linarith

#print axioms rectangularAbsoluteMass_lower
#print axioms rectangularAbsoluteMass_eventually_lower
#print axioms rectangularAbsoluteMass_not_tendsto_zero
end Erdos371
