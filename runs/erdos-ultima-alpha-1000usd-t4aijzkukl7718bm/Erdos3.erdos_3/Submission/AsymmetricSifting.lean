import Submission.LocalCorrelationSifting

/-! Asymmetric local dependent random choice. The two sifted sets need not have the
same localization scale. These are auxiliary results, not the original conjecture. -/
namespace Erdos3AsymmetricSifting
open Finset Erdos3CorrelationSifting Erdos3CorrelationMoments Erdos3LocalCorrelationCentering
  Erdos3LocalCorrelationSifting Erdos3BohrLocalAverages Erdos3BohrTranslation
  Erdos3PopularAlmostPeriods Erdos3WeightedCorrelation
open scoped BigOperators Classical
set_option maxHeartbeats 2500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def crossPairDensity (C D : Finset G) (q : G → ℝ) : ℝ :=
  𝔼 x : G, 𝔼 y : G, indicator C x*indicator D y*q (y-x)

noncomputable def crossAverage (C D : Finset G) (f : G → ℝ) : ℝ :=
  𝔼 c : C, 𝔼 d : D, f ((d : G)-(c : G))

lemma crossPairDensity_one (C D : Finset G) :
    crossPairDensity C D (fun _ ↦ 1) = density C*density D := by
  simp only [crossPairDensity, mul_one, ← Fintype.expect_mul_expect, expect_indicator]

lemma crossPairDensity_nonneg (C D : Finset G) (q : G → ℝ) (hq : ∀ t, 0 ≤ q t) :
    0 ≤ crossPairDensity C D q := by
  apply expect_nonneg
  intro x _
  apply expect_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (indicator_nonneg C x) (indicator_nonneg D y)) (hq _)

lemma crossPairDensity_eq_corr_pairing (C D : Finset G) (q : G → ℝ) :
    crossPairDensity C D q = 𝔼 t : G, crossCorr (indicator C) (indicator D) t*q t := by
  calc
    _ = 𝔼 x : G, 𝔼 t : G, indicator C x*indicator D (x+t)*q t := by
      unfold crossPairDensity
      apply expect_congr rfl
      intro x _
      exact (Fintype.expect_equiv (Equiv.addRight x) _ _ (fun t ↦ by
        change indicator C x*indicator D (x+t)*q t =
          indicator C x*indicator D (t+x)*q (t+x-x)
        rw [add_comm t x]
        have he : x+t-x = t := by abel
        rw [he])).symm
    _ = 𝔼 t : G, 𝔼 x : G, indicator C x*indicator D (x+t)*q t := expect_comm _ _ _
    _ = _ := by simp only [crossCorr, expect_mul]

lemma crossPairDensity_eq_crossAverage (C D : Finset G) (hC : C.Nonempty) (hD : D.Nonempty)
    (q : G → ℝ) :
    crossPairDensity C D q = (density C*density D)*crossAverage C D q := by
  unfold crossPairDensity crossAverage
  simp_rw [mul_assoc, ← mul_expect, expect_indicator_mul D hD]
  rw [expect_indicator_mul C hC]
  simp_rw [← mul_expect]

lemma crossCorr_normalized (C D : Finset G) (t : G) :
    crossCorr (normalized C) (normalized D) t =
      crossCorr (indicator C) (indicator D) t/(density C*density D) := by
  unfold crossCorr normalized
  simp_rw [div_mul_div_comm]
  exact (expect_div ..).symm

lemma crossCorr_indicator_eq (C D : Finset G) (hC : C.Nonempty) (hD : D.Nonempty) (t : G) :
    crossCorr (indicator C) (indicator D) t =
      (density C*density D)*crossCorr (normalized C) (normalized D) t := by
  rw [crossCorr_normalized]
  field_simp [(density_pos C hC).ne', (density_pos D hD).ne']

lemma crossAverage_eq_pairing (C D : Finset G) (hC : C.Nonempty) (hD : D.Nonempty)
    (q : G → ℝ) :
    crossAverage C D q = 𝔼 t : G, crossCorr (normalized C) (normalized D) t*q t := by
  have h := crossPairDensity_eq_crossAverage C D hC hD q
  rw [crossPairDensity_eq_corr_pairing] at h
  simp_rw [crossCorr_indicator_eq C D hC hD, mul_assoc, ← mul_expect] at h
  exact (mul_left_cancel₀ (density_pos D hD).ne' (mul_left_cancel₀ (density_pos C hC).ne' h)).symm

lemma crossCorr_indicator_nonneg (C D : Finset G) (t : G) :
    0 ≤ crossCorr (indicator C) (indicator D) t :=
  expect_nonneg (fun x _ ↦ mul_nonneg (indicator_nonneg C x) (indicator_nonneg D _))

lemma mean_crossCorr_indicator (C D : Finset G) :
    (𝔼 t : G, crossCorr (indicator C) (indicator D) t) = density C*density D := by
  simpa only [mul_one, crossPairDensity_one] using
    (crossPairDensity_eq_corr_pairing C D (fun _ ↦ 1)).symm

lemma expect_asymmetric_localCommon_pair (A C D V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ) (x y : G) :
    (𝔼 v : Fin p → V,
      indicator (localCommon A C (fun i ↦ (v i : G))) x *
      indicator (localCommon A D (fun i ↦ (v i : G))) y) =
      indicator C x*indicator D y*(corr (indicator A) (y-x)/density V)^p := by
  simp_rw [indicator_localCommon]
  have he (v : Fin p → V) :
      (indicator C x * ∏ i, indicator A (x+(v i : G))) *
      (indicator D y * ∏ i, indicator A (y+(v i : G))) =
      (indicator C x*indicator D y) *
        ∏ i, indicator A (x+(v i : G))*indicator A (y+(v i : G)) := by
    rw [prod_mul_distrib]
    ring
  simp_rw [he]
  rw [← mul_expect,
    ← expect_pow_eq (fun z : V ↦ indicator A (x+(z : G))*indicator A (y+(z : G))) p]
  by_cases hx : x ∈ C
  · rw [restricted_corr_gram A C V hV hsupport hx y]
  · simp [indicator, hx]

/-- Only A-C must lie in the sample domain: support of the first factor suffices. -/
theorem expect_crossPairDensity_localCommon (A C D V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (q : G → ℝ) (p : ℕ) :
    (𝔼 v : Fin p → V, crossPairDensity
      (localCommon A C (fun i ↦ (v i : G))) (localCommon A D (fun i ↦ (v i : G))) q) =
      𝔼 t : G, crossCorr (indicator C) (indicator D) t*
        (corr (indicator A) t/density V)^p*q t := by
  unfold crossPairDensity
  calc
    _ = 𝔼 x : G, 𝔼 y : G, 𝔼 v : Fin p → V,
        indicator (localCommon A C (fun i ↦ (v i : G))) x *
        indicator (localCommon A D (fun i ↦ (v i : G))) y * q (y-x) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro x _
      exact expect_comm _ _ _
    _ = crossPairDensity C D (fun t ↦ (corr (indicator A) t/density V)^p*q t) := by
      simp_rw [← expect_mul, expect_asymmetric_localCommon_pair A C D V hV hsupport]
      unfold crossPairDensity
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro y _
      ring
    _ = _ := by
      rw [crossPairDensity_eq_corr_pairing]
      apply expect_congr rfl
      intro t _
      ring

lemma expect_density_localCommon_mul (A C D V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ) :
    (𝔼 v : Fin p → V,
      density (localCommon A C (fun i ↦ (v i : G)))*density (localCommon A D (fun i ↦ (v i : G)))) =
      𝔼 t : G, crossCorr (indicator C) (indicator D) t*(corr (indicator A) t/density V)^p := by
  simpa only [crossPairDensity_one, mul_one] using
    expect_crossPairDensity_localCommon A C D V hV hsupport (fun _ ↦ 1) p

lemma asymmetric_bad_pairs_le (A C D V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ)
    {σ L : ℝ} (hσ : 0 < σ) (hL : 0 ≤ L) :
    (𝔼 v : Fin p → V, crossPairDensity
      (localCommon A C (fun i ↦ (v i : G))) (localCommon A D (fun i ↦ (v i : G)))
      (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0)) ≤
      (density C*density D)*(σ*L/density V)^p := by
  rw [expect_crossPairDensity_localCommon A C D V hV hsupport]
  have hν := density_pos V hV
  calc
    _ ≤ 𝔼 t : G, crossCorr (indicator C) (indicator D) t*(σ*L/density V)^p := by
      apply expect_le_expect
      intro t _
      by_cases ht : corr (indicator A) t/σ ≤ L
      · rw [if_pos ht, mul_one]
        apply mul_le_mul_of_nonneg_left _ (crossCorr_indicator_nonneg C D t)
        apply pow_le_pow_left₀ (div_nonneg (corr_indicator_nonneg A t) hν.le)
        apply div_le_div_of_nonneg_right _ hν.le
        have ht' := (div_le_iff₀ hσ).mp ht
        nlinarith
      · rw [if_neg ht, mul_zero]
        exact mul_nonneg (crossCorr_indicator_nonneg C D t)
          (pow_nonneg (div_nonneg (mul_nonneg hσ.le hL) hν.le) p)
    _ = _ := by rw [← expect_mul, mean_crossCorr_indicator]

/-- A large cross-weighted moment selects two localized intersections with a large
product of densities and few bad cross-pairs. -/
theorem exists_asymmetric_sifted_intersections (A C D V : Finset G)
    (hC : C.Nonempty) (hD : D.Nonempty) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ)
    {σ L H : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hH : 0 < H)
    (hmoment : H^p ≤ 𝔼 t : G, crossCorr (normalized C) (normalized D) t*
      (corr (indicator A) t/σ)^p) :
    ∃ v : Fin p → V,
      (localCommon A C (fun i ↦ (v i : G))).Nonempty ∧
      (localCommon A D (fun i ↦ (v i : G))).Nonempty ∧
      (density C*density D)*(σ*H/density V)^p ≤
        2*density (localCommon A C (fun i ↦ (v i : G)))*density (localCommon A D (fun i ↦ (v i : G))) ∧
      crossPairDensity (localCommon A C (fun i ↦ (v i : G)))
        (localCommon A D (fun i ↦ (v i : G)))
        (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0) ≤
        2*(L/H)^p*density (localCommon A C (fun i ↦ (v i : G)))*
          density (localCommon A D (fun i ↦ (v i : G))) := by
  letI : Nonempty V := hV.to_subtype
  have hγ := density_pos C hC
  have hη := density_pos D hD
  have hν := density_pos V hV
  let M := (density C*density D)*(σ*H/density V)^p
  let B := (density C*density D)*(σ*L/density V)^p
  have hM : 0 < M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hm : M ≤ 𝔼 v : Fin p → V,
      density (localCommon A C (fun i ↦ (v i : G)))*density (localCommon A D (fun i ↦ (v i : G))) := by
    rw [expect_density_localCommon_mul A C D V hV hsupport]
    have he (t : G) : crossCorr (indicator C) (indicator D) t*(corr (indicator A) t/density V)^p =
        ((density C*density D)*(σ/density V)^p) *
          (crossCorr (normalized C) (normalized D) t*(corr (indicator A) t/σ)^p) := by
      rw [crossCorr_indicator_eq C D hC hD]
      have hr : corr (indicator A) t/density V = (σ/density V)*(corr (indicator A) t/σ) := by field_simp
      rw [hr, mul_pow]
      ring
    simp_rw [he, ← mul_expect]
    calc
      M = ((density C*density D)*(σ/density V)^p)*H^p := by
        dsimp [M]
        have hr : σ*H/density V = (σ/density V)*H := by ring
        rw [hr, mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (by positivity)
  obtain ⟨v,hvs,hvb⟩ := select_weight_cost
    (fun v : Fin p → V ↦ density (localCommon A C (fun i ↦ (v i : G)))*
      density (localCommon A D (fun i ↦ (v i : G))))
    (fun v ↦ crossPairDensity (localCommon A C (fun i ↦ (v i : G)))
      (localCommon A D (fun i ↦ (v i : G)))
      (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0)) hM hB
    (fun v ↦ crossPairDensity_nonneg _ _ _ (fun t ↦ by split_ifs <;> norm_num)) hm
    (asymmetric_bad_pairs_le A C D V hV hsupport p hσ hL.le)
  have hneC : (localCommon A C (fun i ↦ (v i : G))).Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    simp only [hz, density, card_empty, Nat.cast_zero, zero_div, zero_mul, mul_zero] at hvs
    linarith
  have hneD : (localCommon A D (fun i ↦ (v i : G))).Nonempty := by
    by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    simp only [hz, density, card_empty, Nat.cast_zero, zero_div, zero_mul, mul_zero] at hvs
    linarith
  refine ⟨v,hneC,hneD,by simpa only [M, mul_assoc] using hvs,?_⟩
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    M*crossPairDensity (localCommon A C (fun i ↦ (v i : G)))
        (localCommon A D (fun i ↦ (v i : G)))
        (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0) ≤
        2*B*(density (localCommon A C (fun i ↦ (v i : G)))*
          density (localCommon A D (fun i ↦ (v i : G)))) := hvb
    _ = _ := by
      dsimp [M,B]
      have he : σ*L/density V = (σ*H/density V)*(L/H) := by field_simp
      rw [he, mul_pow]
      ring

lemma relativeDensity_le_one (S C : Finset G) (hC : C.Nonempty) : relativeDensity S C ≤ 1 := by
  unfold relativeDensity
  apply (div_le_one (by exact_mod_cast hC.card_pos : (0 : ℝ) < C.card)).mpr
  exact_mod_cast card_le_card (inter_subset_right (s₁ := S) (s₂ := C))

/-- Relative asymmetric sifting: both factors retain relative density at least α^(2p)/2. -/
theorem exists_relative_asymmetric_sets (A B C D V : Finset G)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hC : C.Nonempty) (hD : D.Nonempty) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ)
    {L H : ℝ} (hL : 0 < L) (hH : 0 < H) (hVsize : density V ≤ H*density B)
    (hmoment : H^p ≤ 𝔼 t : G, crossCorr (normalized C) (normalized D) t*
      (corr (localNormalized A B) t/density B)^p) :
    ∃ S ⊆ C, ∃ T ⊆ D, S.Nonempty ∧ T.Nonempty ∧
      (relativeDensity A B)^(2*p) ≤ 2*relativeDensity S C ∧
      (relativeDensity A B)^(2*p) ≤ 2*relativeDensity T D ∧
      crossPairDensity S T (fun t ↦ if corr (localNormalized A B) t/density B ≤ L then 1 else 0) ≤
        2*(L/H)^p*density S*density T := by
  have hα := relativeDensity_pos A B hA hAB
  have hβ := density_pos B (hA.mono hAB)
  have hγ := density_pos C hC
  have hη := density_pos D hD
  have hν := density_pos V hV
  let σ := (relativeDensity A B)^2*density B
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have he (t : G) : corr (localNormalized A B) t/density B = corr (indicator A) t/σ := by
    rw [corr_localNormalized, div_div]
  have hm : H^p ≤ 𝔼 t : G, crossCorr (normalized C) (normalized D) t*(corr (indicator A) t/σ)^p := by
    simpa only [he] using hmoment
  obtain ⟨v,hS,hT,hvs,hvb⟩ := exists_asymmetric_sifted_intersections A C D V hC hD hV hsupport p hσ hL hH hm
  let S := localCommon A C (fun i ↦ (v i : G))
  let T := localCommon A D (fun i ↦ (v i : G))
  have hSC : S ⊆ C := localCommon_subset ..
  have hTD : T ⊆ D := localCommon_subset ..
  have hratio : (relativeDensity A B)^2 ≤ σ*H/density V := by
    apply (le_div_iff₀ hν).mpr
    have h := mul_le_mul_of_nonneg_left hVsize (sq_nonneg (relativeDensity A B))
    dsimp [σ]
    nlinarith
  have hraw : (density C*density D)*(relativeDensity A B)^(2*p) ≤ 2*density S*density T := by
    calc
      _ = (density C*density D)*((relativeDensity A B)^2)^p := by rw [pow_mul]
      _ ≤ (density C*density D)*(σ*H/density V)^p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hratio p) (mul_nonneg hγ.le hη.le)
      _ ≤ _ := hvs
  have hprod : (relativeDensity A B)^(2*p) ≤ 2*relativeDensity S C*relativeDensity T D := by
    apply (mul_le_mul_iff_right₀ (mul_pos hγ hη)).mp
    calc
      _ ≤ 2*density S*density T := hraw
      _ = _ := by
        rw [density_eq_relative_mul S C hS hSC, density_eq_relative_mul T D hT hTD]
        ring
  have hSpos := relativeDensity_pos S C hS hSC
  have hTpos := relativeDensity_pos T D hT hTD
  refine ⟨S,hSC,T,hTD,hS,hT,?_,?_,?_⟩
  · exact hprod.trans (by nlinarith [relativeDensity_le_one T D hD])
  · exact hprod.trans (by nlinarith [relativeDensity_le_one S C hC])
  · simpa only [he] using hvb

#print axioms crossAverage_eq_pairing
#print axioms expect_crossPairDensity_localCommon
#print axioms exists_asymmetric_sifted_intersections
#print axioms exists_relative_asymmetric_sets
end Erdos3AsymmetricSifting
