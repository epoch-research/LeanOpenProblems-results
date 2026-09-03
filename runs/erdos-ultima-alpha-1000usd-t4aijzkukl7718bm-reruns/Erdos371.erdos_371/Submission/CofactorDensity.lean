import FormalConjecturesUtil

/-! Density-zero bounds for bounded largest-prime cofactors. -/

open Filter
open scoped Topology

namespace Erdos371CofactorDensity

lemma primeCounting_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => (Real.log 4 + 1) / Real.log N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hlog) :
        Tendsto (fun N : ℕ => (Real.log 4 + 1) * (Real.log N)⁻¹)
          atTop (𝓝 ((Real.log 4 + 1) * 0)))
  have hb : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤ (Real.log 4 + 1) * N / Real.log N := by
    simpa using
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => by positivity
  · filter_upwards [hb, eventually_gt_atTop 0] with N hN hpos
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hpos
    apply (div_le_iff₀ hn).mpr
    simpa [div_mul_eq_mul_div] using hN

lemma bounded_cofactor_count (K N : ℕ) :
    ((Finset.range N).filter (fun n => n / Nat.maxPrimeFac n ≤ K)).card ≤
      (K + 1) * (Nat.primeCounting N + 1) := by
  let B := insert 1 (N + 1).primesBelow
  let F := ((Finset.range (K + 1)).product B).image (fun ap : ℕ × ℕ => ap.1 * ap.2)
  have hsub : (Finset.range N).filter (fun n => n / Nat.maxPrimeFac n ≤ K) ⊆ F := by
    intro n hn
    obtain ⟨hr, hK⟩ := Finset.mem_filter.mp hn
    have hnN : n < N := Finset.mem_range.mp hr
    by_cases hn0 : n = 0
    · subst n
      apply Finset.mem_image.mpr
      refine ⟨(0, 1), ?_, by simp⟩
      simp [B]
    · have hpB : Nat.maxPrimeFac n ∈ B := by
        by_cases hn1 : n = 1
        · simp [B, hn1]
        · apply Finset.mem_insert_of_mem
          exact Nat.mem_primesBelow.mpr
            ⟨by have := Nat.maxPrimeFac_le (n := n); omega,
              Nat.prime_maxPrimeFac_of_one_lt n (by omega)⟩
      apply Finset.mem_image.mpr
      refine ⟨(n / Nat.maxPrimeFac n, Nat.maxPrimeFac n), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hpB⟩
      · exact Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  have hB : B.card ≤ Nat.primeCounting N + 1 := by
    calc
      B.card ≤ (N + 1).primesBelow.card + 1 := Finset.card_insert_le _ _
      _ = Nat.primeCounting N + 1 := by
        rw [Nat.primesBelow_card_eq_primeCounting']
        rfl
  calc
    ((Finset.range N).filter (fun n => n / Nat.maxPrimeFac n ≤ K)).card ≤ F.card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.range (K + 1)).product B).card := Finset.card_image_le
    _ = (K + 1) * B.card := by simp
    _ ≤ (K + 1) * (Nat.primeCounting N + 1) := Nat.mul_le_mul_left _ hB

lemma bounded_cofactor_partialDensity (K N : ℕ) :
    {n | n / Nat.maxPrimeFac n ≤ K}.partialDensity Set.univ N =
      (((Finset.range N).filter (fun n => n / Nat.maxPrimeFac n ≤ K)).card : ℝ) / N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have he : {n | n / Nat.maxPrimeFac n ≤ K} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => n / Nat.maxPrimeFac n ≤ K)) := by
    ext n
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma bounded_cofactor_hasDensity_zero (K : ℕ) :
    {n | n / Nat.maxPrimeFac n ≤ K}.HasDensity 0 := by
  have hu : Tendsto (fun N : ℕ =>
      (K + 1 : ℝ) * ((Nat.primeCounting N : ℝ) + 1) / N) atTop (𝓝 0) := by
    simpa [mul_div_assoc, add_div] using
      (tendsto_const_nhds.mul
        (primeCounting_ratio_tendsto_zero.add tendsto_one_div_atTop_nhds_zero_nat) :
        Tendsto (fun N : ℕ =>
          (K + 1 : ℝ) * ((Nat.primeCounting N : ℝ) / N + 1 / N))
          atTop (𝓝 ((K + 1 : ℝ) * (0 + 0))))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    change {n | n / Nat.maxPrimeFac n ≤ K}.partialDensity Set.univ N ≤ _
    rw [bounded_cofactor_partialDensity]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast bounded_cofactor_count K N

lemma density_zero_shift {S : Set ℕ} (hS : S.HasDensity 0) :
    {n | n + 1 ∈ S}.HasDensity 0 := by
  have hu : Tendsto (fun N : ℕ => 2 * S.partialDensity Set.univ (N + 1))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hS.comp (tendsto_add_atTop_nat 1)) :
      Tendsto (fun N : ℕ => 2 * S.partialDensity Set.univ (N + 1)) atTop (𝓝 (2 * 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => by unfold Set.partialDensity; positivity
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hsub : (fun n : ℕ => n + 1) '' ({n | n + 1 ∈ S} ∩ Set.Iio N) ⊆
        S ∩ Set.Iio (N + 1) := by
      rintro _ ⟨n, ⟨hnS, hnN⟩, rfl⟩
      exact ⟨hnS, by change n + 1 < N + 1; exact Nat.add_lt_add_right hnN 1⟩
    have hc : ({n | n + 1 ∈ S} ∩ Set.Iio N).ncard ≤ (S ∩ Set.Iio (N + 1)).ncard := by
      calc
        _ = ((fun n : ℕ => n + 1) '' ({n | n + 1 ∈ S} ∩ Set.Iio N)).ncard :=
          (Set.ncard_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)).symm
        _ ≤ _ := Set.ncard_le_ncard hsub
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    rw [← mul_div_assoc]
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hNr' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    calc
      _ ≤ ((S ∩ Set.Iio (N + 1)).ncard : ℝ) / N :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) hNr.le
      _ ≤ _ := by
        apply (div_le_div_iff₀ hNr hNr').mpr
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have hnonneg : (0 : ℝ) ≤ (S ∩ Set.Iio (N + 1)).ncard := Nat.cast_nonneg _
        push_cast
        nlinarith

lemma density_zero_union {S T : Set ℕ} (hS : S.HasDensity 0) (hT : T.HasDensity 0) :
    (S ∪ T).HasDensity 0 := by
  have hu : Tendsto (fun N : ℕ => S.partialDensity Set.univ N + T.partialDensity Set.univ N)
      atTop (𝓝 0) := by simpa using hS.add hT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    have hc : ((S ∪ T) ∩ Set.Iio N).ncard ≤
        (S ∩ Set.Iio N).ncard + (T ∩ Set.Iio N).ncard := by
      rw [Set.union_inter_distrib_right]
      exact Set.ncard_union_le _ _
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact_mod_cast hc

lemma bounded_cofactor_pair_hasDensity_zero (K : ℕ) :
    {n | n / Nat.maxPrimeFac n ≤ K ∨ (n + 1) / Nat.maxPrimeFac (n + 1) ≤ K}.HasDensity 0 := by
  have h1 := bounded_cofactor_hasDensity_zero K
  have h2 : {n | (n + 1) / Nat.maxPrimeFac (n + 1) ≤ K}.HasDensity 0 :=
    density_zero_shift (S := {n | n / Nat.maxPrimeFac n ≤ K}) h1
  exact density_zero_union (S := {n | n / Nat.maxPrimeFac n ≤ K})
    (T := {n | (n + 1) / Nat.maxPrimeFac (n + 1) ≤ K}) h1 h2

end Erdos371CofactorDensity

#print axioms Erdos371CofactorDensity.primeCounting_ratio_tendsto_zero
#print axioms Erdos371CofactorDensity.bounded_cofactor_hasDensity_zero

#print axioms Erdos371CofactorDensity.bounded_cofactor_pair_hasDensity_zero
