import Submission.LocalCorrelationCentering
import Submission.DoubledWeights

/-! Localized dependent-random-choice sifting. Sample shifts are restricted to a set
containing A-C, so the density loss depends on the relative density rather than the
ambient density of the base set. Auxiliary results only. -/
namespace Erdos3LocalCorrelationSifting
open Finset Erdos3CorrelationSifting Erdos3CorrelationMoments Erdos3FiniteSampling
  Erdos3WeightedCorrelation Erdos3BohrTranslation Erdos3BohrLocalAverages
  Erdos3LocalCorrelationCentering Erdos3PopularAlmostPeriods Erdos3FiniteBohr
  Erdos3BohrCovering
open scoped BigOperators Classical
set_option maxHeartbeats 2500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def localCommon {I : Type*} [Fintype I]
    (A C : Finset G) (v : I → G) : Finset G := C ∩ common A v

lemma localCommon_subset {I : Type*} [Fintype I] (A C : Finset G) (v : I → G) :
    localCommon A C v ⊆ C := inter_subset_left

lemma indicator_localCommon {I : Type*} [Fintype I]
    (A C : Finset G) (v : I → G) (x : G) :
    indicator (localCommon A C v) x = indicator C x*∏ i, indicator A (x+v i) := by
  rw [← indicator_common]
  by_cases hx : x ∈ C <;> by_cases hy : x ∈ common A v <;>
    simp [localCommon, indicator, hx, hy]

lemma expect_restrict (V : Finset G) (hV : V.Nonempty) (f : G → ℝ)
    (hf : ∀ x, x ∉ V → f x = 0) :
    (𝔼 v : V, f v) = (𝔼 x : G, f x)/density V := by
  rw [← expect_normalized_mul V hV]
  have he (x : G) : normalized V x*f x = f x/density V := by
    by_cases hx : x ∈ V
    · simp [normalized, indicator, hx, div_eq_mul_inv, mul_comm]
    · simp [normalized, indicator, hx, hf x hx]
  simp_rw [he]
  exact (expect_div ..).symm

lemma restricted_corr_gram (A C V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V)
    {x : G} (hx : x ∈ C) (y : G) :
    (𝔼 v : V, indicator A (x+(v : G))*indicator A (y+(v : G))) =
      corr (indicator A) (y-x)/density V := by
  rw [expect_restrict V hV (fun z : G ↦ indicator A (x+z)*indicator A (y+z)), ← corr_gram]
  intro z hz
  have hn : x+z ∉ A := by
    intro ha
    have h := hsupport (x+z) ha x hx
    have he : x+z-x = z := by abel
    exact hz (he ▸ h)
  simp [indicator, hn]

lemma expect_localCommon_pair (A C V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ) (x y : G) :
    (𝔼 v : Fin p → V,
      indicator (localCommon A C (fun i ↦ (v i : G))) x *
      indicator (localCommon A C (fun i ↦ (v i : G))) y) =
      indicator C x*indicator C y*(corr (indicator A) (y-x)/density V)^p := by
  simp_rw [indicator_localCommon]
  have he (v : Fin p → V) :
      (indicator C x * ∏ i, indicator A (x+(v i : G))) *
      (indicator C y * ∏ i, indicator A (y+(v i : G))) =
      (indicator C x*indicator C y) *
        ∏ i, indicator A (x+(v i : G))*indicator A (y+(v i : G)) := by
    rw [prod_mul_distrib]
    ring
  simp_rw [he]
  rw [← mul_expect]
  rw [← expect_pow_eq (fun z : V ↦ indicator A (x+(z : G))*indicator A (y+(z : G))) p]
  by_cases hx : x ∈ C
  · rw [restricted_corr_gram A C V hV hsupport hx y]
  · simp [indicator, hx]

lemma pairDensity_eq_corr_pairing (C : Finset G) (q : G → ℝ) :
    pairDensity C q = 𝔼 t : G, corr (indicator C) t*q t := by
  calc
    pairDensity C q = 𝔼 x : G, 𝔼 t : G, indicator C x*indicator C (x+t)*q t := by
      unfold pairDensity
      apply expect_congr rfl
      intro x _
      exact (Fintype.expect_equiv (Equiv.addRight x) _ _ (fun t ↦ by
        change indicator C x*indicator C (x+t)*q t =
          indicator C x*indicator C (t+x)*q (t+x-x)
        rw [add_comm t x]
        have he : x+t-x = t := by abel
        rw [he])).symm
    _ = 𝔼 t : G, 𝔼 x : G, indicator C x*indicator C (x+t)*q t := expect_comm _ _ _
    _ = _ := by simp only [corr, expect_mul]

/-- Exact restricted-sampling identity for pair costs. -/
theorem expect_pairDensity_localCommon (A C V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (q : G → ℝ) (p : ℕ) :
    (𝔼 v : Fin p → V, pairDensity (localCommon A C (fun i ↦ (v i : G))) q) =
      𝔼 t : G, corr (indicator C) t*(corr (indicator A) t/density V)^p*q t := by
  unfold pairDensity
  calc
    _ = 𝔼 x : G, 𝔼 y : G, 𝔼 v : Fin p → V,
        indicator (localCommon A C (fun i ↦ (v i : G))) x *
        indicator (localCommon A C (fun i ↦ (v i : G))) y * q (y-x) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro x _
      exact expect_comm _ _ _
    _ = pairDensity C (fun t ↦ (corr (indicator A) t/density V)^p*q t) := by
      simp_rw [← expect_mul, expect_localCommon_pair A C V hV hsupport]
      unfold pairDensity
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro y _
      ring
    _ = _ := by
      rw [pairDensity_eq_corr_pairing]
      apply expect_congr rfl
      intro t _
      ring

lemma expect_density_localCommon_sq (A C V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ) :
    (𝔼 v : Fin p → V, (density (localCommon A C (fun i ↦ (v i : G))))^2) =
      𝔼 t : G, corr (indicator C) t*(corr (indicator A) t/density V)^p := by
  simpa only [pairDensity_one, mul_one] using
    expect_pairDensity_localCommon A C V hV hsupport (fun _ ↦ 1) p

lemma local_bad_pairs_le (A C V : Finset G) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ)
    {σ L : ℝ} (hσ : 0 < σ) (hL : 0 ≤ L) :
    (𝔼 v : Fin p → V, pairDensity (localCommon A C (fun i ↦ (v i : G)))
      (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0)) ≤
      (density C)^2*(σ*L/density V)^p := by
  rw [expect_pairDensity_localCommon A C V hV hsupport]
  have hν := density_pos V hV
  calc
    _ ≤ 𝔼 t : G, corr (indicator C) t*(σ*L/density V)^p := by
      apply expect_le_expect
      intro t _
      by_cases ht : corr (indicator A) t/σ ≤ L
      · rw [if_pos ht, mul_one]
        apply mul_le_mul_of_nonneg_left _ (corr_indicator_nonneg C t)
        apply pow_le_pow_left₀ (div_nonneg (corr_indicator_nonneg A t) hν.le)
        apply div_le_div_of_nonneg_right _ hν.le
        have ht' := (div_le_iff₀ hσ).mp ht
        nlinarith
      · rw [if_neg ht, mul_zero]
        exact mul_nonneg (corr_indicator_nonneg C t)
          (pow_nonneg (div_nonneg (mul_nonneg hσ.le hL) hν.le) p)
    _ = _ := by rw [← expect_mul, mean_corr, expect_indicator]

/-- Local sifting with a freely chosen correlation scale. The cost of restricting the
sample shifts is exactly the displayed density ratio σ/density(V). -/
theorem exists_local_sifted_intersection (A C V : Finset G) (hC : C.Nonempty) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ)
    {σ L H : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hH : 0 < H)
    (hmoment : H^p ≤ 𝔼 t : G, corr (normalized C) t*(corr (indicator A) t/σ)^p) :
    ∃ v : Fin p → V,
      (localCommon A C (fun i ↦ (v i : G))).Nonempty ∧
      (density C)^2*(σ*H/density V)^p ≤
        2*(density (localCommon A C (fun i ↦ (v i : G))))^2 ∧
      pairDensity (localCommon A C (fun i ↦ (v i : G)))
        (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0) ≤
        2*(L/H)^p*(density (localCommon A C (fun i ↦ (v i : G))))^2 := by
  letI : Nonempty V := hV.to_subtype
  have hγ := density_pos C hC
  have hν := density_pos V hV
  let M := (density C)^2*(σ*H/density V)^p
  let B := (density C)^2*(σ*L/density V)^p
  have hM : 0 < M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hm : M ≤ 𝔼 v : Fin p → V,
      (density (localCommon A C (fun i ↦ (v i : G))))^2 := by
    rw [expect_density_localCommon_sq A C V hV hsupport]
    have he (t : G) : corr (indicator C) t*(corr (indicator A) t/density V)^p =
        ((density C)^2*(σ/density V)^p) *
          (corr (normalized C) t*(corr (indicator A) t/σ)^p) := by
      rw [corr_indicator_eq C hC]
      have hr : corr (indicator A) t/density V = (σ/density V)*(corr (indicator A) t/σ) := by
        field_simp
      rw [hr, mul_pow]
      ring
    simp_rw [he, ← mul_expect]
    calc
      M = ((density C)^2*(σ/density V)^p)*H^p := by
        dsimp [M]
        rw [mul_assoc, ← mul_pow]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmoment (by positivity)
  obtain ⟨v,hvs,hvb⟩ := select_weight_cost
    (fun v : Fin p → V ↦ (density (localCommon A C (fun i ↦ (v i : G))))^2)
    (fun v ↦ pairDensity (localCommon A C (fun i ↦ (v i : G)))
      (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0)) hM hB
    (fun v ↦ pairDensity_nonneg _ _ (fun t ↦ by split_ifs <;> norm_num)) hm
    (local_bad_pairs_le A C V hV hsupport p hσ hL.le)
  refine ⟨v,?_,hvs,?_⟩
  · by_contra hn
    have hz := not_nonempty_iff_eq_empty.mp hn
    simp only [hz, density, card_empty, Nat.cast_zero, zero_div,
      zero_pow (by decide : 2 ≠ 0), mul_zero] at hvs
    linarith
  · apply (mul_le_mul_iff_right₀ hM).mp
    calc
      M*pairDensity (localCommon A C (fun i ↦ (v i : G)))
          (fun t ↦ if corr (indicator A) t/σ ≤ L then 1 else 0) ≤
          2*B*(density (localCommon A C (fun i ↦ (v i : G))))^2 := hvb
      _ = M*(2*(L/H)^p*(density (localCommon A C (fun i ↦ (v i : G))))^2) := by
        dsimp [M,B]
        have he : σ*L/density V = (σ*H/density V)*(L/H) := by field_simp
        rw [he, mul_pow]
        ring

lemma corr_localNormalized (A B : Finset G) (t : G) :
    corr (localNormalized A B) t = corr (indicator A) t/(relativeDensity A B)^2 := by
  unfold corr localNormalized
  simp_rw [div_mul_div_comm, ← sq]
  exact (expect_div ..).symm

/-- If the sampling domain is only a controlled enlargement of the base, the sifted
set retains relative density α^p/2 inside C. No power of the ambient base density remains. -/
theorem exists_relative_sifted_intersection (A B C V : Finset G)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hC : C.Nonempty) (hV : V.Nonempty)
    (hsupport : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ V) (p : ℕ)
    {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    (hVsize : density V ≤ H*density B)
    (hmoment : H^p ≤ 𝔼 t : G, corr (normalized C) t*
      (corr (localNormalized A B) t/density B)^p) :
    ∃ v : Fin p → V,
      (localCommon A C (fun i ↦ (v i : G))).Nonempty ∧
      (relativeDensity A B)^p ≤ 2*relativeDensity (localCommon A C (fun i ↦ (v i : G))) C ∧
      pairDensity (localCommon A C (fun i ↦ (v i : G)))
        (fun t ↦ if corr (localNormalized A B) t/density B ≤ L then 1 else 0) ≤
        2*(L/H)^p*(density (localCommon A C (fun i ↦ (v i : G))))^2 := by
  have hα := relativeDensity_pos A B hA hAB
  have hβ := density_pos B (hA.mono hAB)
  have hγ := density_pos C hC
  have hν := density_pos V hV
  let σ := (relativeDensity A B)^2*density B
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have he (t : G) : corr (localNormalized A B) t/density B = corr (indicator A) t/σ := by
    rw [corr_localNormalized, div_div]
  have hm : H^p ≤ 𝔼 t : G, corr (normalized C) t*(corr (indicator A) t/σ)^p := by
    simpa only [he] using hmoment
  obtain ⟨v,hvne,hvs,hvb⟩ := exists_local_sifted_intersection A C V hC hV hsupport p hσ hL hH hm
  refine ⟨v,hvne,?_,?_⟩
  · have hratio : (relativeDensity A B)^2 ≤ σ*H/density V := by
      apply (le_div_iff₀ hν).mpr
      have h := mul_le_mul_of_nonneg_left hVsize (sq_nonneg (relativeDensity A B))
      dsimp [σ]
      nlinarith
    have hsq : (density C*(relativeDensity A B)^p)^2 ≤
        2*(density (localCommon A C (fun i ↦ (v i : G))))^2 := by
      calc
        _ = (density C)^2*((relativeDensity A B)^2)^p := by ring
        _ ≤ (density C)^2*(σ*H/density V)^p := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sq_nonneg _) hratio p) (sq_nonneg _)
        _ ≤ _ := hvs
    have hlin : density C*(relativeDensity A B)^p ≤
        2*density (localCommon A C (fun i ↦ (v i : G))) := by
      have hx : 0 ≤ density C*(relativeDensity A B)^p := by positivity
      have hy := density_nonneg (localCommon A C (fun i ↦ (v i : G)))
      apply (pow_le_pow_iff_left₀ hx (mul_nonneg (by norm_num) hy) (by decide : 2 ≠ 0)).mp
      nlinarith [sq_nonneg (density (localCommon A C (fun i ↦ (v i : G))))]
    apply (mul_le_mul_iff_right₀ hγ).mp
    calc
      density C*(relativeDensity A B)^p ≤
          2*density (localCommon A C (fun i ↦ (v i : G))) := hlin
      _ = density C*(2*relativeDensity (localCommon A C (fun i ↦ (v i : G))) C) := by
        rw [density_eq_relative_mul _ C hvne (localCommon_subset ..)]
        ring
  · simpa only [he] using hvb

/-- Bohr-set specialization: only the enlargement factor |B(r+rho)|/|B(r)| is paid. -/
theorem exists_bohr_sifted_set (D : Finset (AddChar G ℂ)) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (A C : Finset G)
    (hA : A.Nonempty) (hAB : A ⊆ bohr D r) (hC : C.Nonempty) (hCsub : C ⊆ bohr D ρ)
    (p : ℕ) {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    (hgrowth : ((bohr D (r+ρ)).card : ℝ) ≤ H*((bohr D r).card : ℝ))
    (hmoment : H^p ≤ 𝔼 t : G, corr (normalized C) t*
      (corr (localNormalized A (bohr D r)) t/density (bohr D r))^p) :
    ∃ S ⊆ C, S.Nonempty ∧ (relativeDensity A (bohr D r))^p ≤ 2*relativeDensity S C ∧
      pairDensity S
        (fun t ↦ if corr (localNormalized A (bohr D r)) t/density (bohr D r) ≤ L then 1 else 0) ≤
        2*(L/H)^p*(density S)^2 := by
  have hs : ∀ a ∈ A, ∀ c ∈ C, a-c ∈ bohr D (r+ρ) := by
    intro a ha c hc
    simpa only [sub_eq_add_neg] using bohr_add (hAB ha) (bohr_neg (hCsub hc))
  have hsize : density (bohr D (r+ρ)) ≤ H*density (bohr D r) := by
    unfold density
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hgrowth (Nat.cast_nonneg _)
  obtain ⟨v,hvne,hvd,hvb⟩ := exists_relative_sifted_intersection A (bohr D r) C (bohr D (r+ρ))
    hA hAB hC ⟨0,bohr_zero D (add_nonneg hr hρ)⟩ hs p hL hH hsize hmoment
  exact ⟨localCommon A C (fun i ↦ (v i : G)),localCommon_subset ..,hvne,hvd,hvb⟩

open Erdos3DoubledWeights Erdos3LocalThreeAPMoment

/-- The conditional local 3AP moment gain now yields a relatively dense subset of the
weight's averaging set, concentrated on popular differences. The center-mass hypothesis
is still explicit. -/
theorem sift_local_threeAPFree (D : Finset (AddChar G ℂ)) {r h ρ δ : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hρh : 2*ρ ≤ h)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A Z C : Finset G) (hA : A.Nonempty) (hAB : A ⊆ bohr D r) (hZA : Z ⊆ A)
    (hfree : ThreeAPFree (A : Set G)) (hC : C.Nonempty) (hCsub : C ⊆ bohr D ρ)
    (hCeven : ∀ x ∈ C, -x ∈ C)
    (hsize : 8 ≤ (relativeDensity A (bohr D r))^2*((bohr D r).card : ℝ))
    (herror : δ*(2/relativeDensity A (bohr D r)+1) ≤ 1/256)
    (hcenters : ∀ a ∈ Z, a+a ∈ bohr D h)
    {p : ℕ} (hp : 0 < p) (hpeven : Even p)
    (hmass : (2/3 : ℝ)^p ≤ doubledMass Z (corr (normalized C))) :
    ∃ S ⊆ C, S.Nonempty ∧ (relativeDensity A (bohr D r))^(8*p) ≤ 2*relativeDensity S C ∧
      pairDensity S
        (fun t ↦ if corr (localNormalized A (bohr D r)) t/density (bohr D r) ≤ 33/32 then 1 else 0) ≤
        2*(33/34 : ℝ)^(8*p)*(density S)^2 := by
  have hα := relativeDensity_pos A (bohr D r) hA hAB
  have hδsmall : δ ≤ 1/16 := by
    have hfactor : 0 ≤ 2/relativeDensity A (bohr D r) := by positivity
    nlinarith
  have hw (t : G) (ht : corr (normalized C) t ≠ 0) : t ∈ bohr D h := by
    obtain ⟨b,hb,c,hc,rfl⟩ := corr_normalized_nonzero C ht
    have hd := bohr_add (hCsub hc) (bohr_neg (hCsub hb))
    exact Erdos3BohrCovering.bohr_mono (D := D) (by linarith : ρ+ρ ≤ h) (by simpa only [sub_eq_add_neg] using hd)
  have hmoment := local_threeAP_weighted_gain D hr hh hδ hgrowth A Z hA hAB hZA hfree
    hsize herror (normalized C) (normalized_nonneg C) (expect_normalized C hC)
    (normalized_even C hCeven) hw hcenters hp hpeven hmass
  have hg : ((bohr D (r+ρ)).card : ℝ) ≤ (17/16 : ℝ)*((bohr D r).card : ℝ) := by
    have houter : ((bohr D (r+ρ)).card : ℝ) ≤ ((bohr D (r+h)).card : ℝ) := by
      exact_mod_cast card_le_card (bohr_mono (D := D) (by linarith : r+ρ ≤ r+h))
    have hinner : ((bohr D (r-h)).card : ℝ) ≤ ((bohr D r).card : ℝ) := by
      exact_mod_cast card_le_card (bohr_mono (D := D) (by linarith : r-h ≤ r))
    calc
      _ ≤ ((bohr D (r+h)).card : ℝ) := houter
      _ ≤ (1+δ)*((bohr D (r-h)).card : ℝ) := hgrowth
      _ ≤ (1+δ)*((bohr D r).card : ℝ) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  obtain ⟨S,hSC,hS,hSd,hSp⟩ := exists_bohr_sifted_set D hr hρ A C hA hAB hC hCsub (8*p)
    (L := 33/32) (H := 17/16) (by norm_num) (by norm_num) hg hmoment
  refine ⟨S,hSC,hS,hSd,?_⟩
  norm_num only [show (33/32 : ℝ)/(17/16) = 33/34 by norm_num] at hSp
  exact hSp

#print axioms expect_pairDensity_localCommon
#print axioms exists_local_sifted_intersection
#print axioms exists_relative_sifted_intersection
#print axioms exists_bohr_sifted_set
#print axioms sift_local_threeAPFree
end Erdos3LocalCorrelationSifting
