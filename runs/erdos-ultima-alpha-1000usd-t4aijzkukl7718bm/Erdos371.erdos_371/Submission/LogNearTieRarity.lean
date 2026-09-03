import Submission.LowLogNearTieBound
import Submission.PrimeBandDensity

/-! Uniform rarity of near-ties on the normalized logarithmic scale.
This is a regularity statement, not an assertion of symmetry of the joint
largest-prime-factor distribution. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

lemma primeDivisorBandSet_eventually_le (u v : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((primeDivisorBandSet N u v).card : ℝ)/N ≤
      8*(v-u)/u+ε := by
  have hH := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hscale := hH.const_mul_atTop hu
  have he : Tendsto (fun N : ℕ => 16/(u*(Real.log N/Real.log 2))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscale
  filter_upwards [he.eventually_lt_const hε, hscale.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℕ)] with N he hs hN
  exact (primeDivisorBandSet_ratio_bound N u v hu huv hN hs).trans (by linarith)

lemma logRatioSet_subset_ranges (N : ℕ) (τ δ : ℝ)
    (hN : 1 < N) (hτ : 0 ≤ τ) (hδ : δ ≤ τ) :
    logRatioSet N δ ⊆ range 2 ∪ lowLogRatioSet N (1/2-τ) δ ∪
      primeDivisorBandSet N (1/2-2*τ) (1/2+2*τ) ∪ highLogRatioSet N (1/2+τ) δ := by
  classical
  intro n hn
  obtain ⟨hnN,hcomp⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hdpos := Real.rpow_pos_of_pos hn0 δ
  by_cases hn2 : 1 < n
  · by_cases hlo : (Nat.maxPrimeFac (n+1) : ℝ) < (N : ℝ)^(1/2-2*τ)
    · apply mem_union_left
      apply mem_union_left
      apply mem_union_right
      apply mem_filter.mpr
      refine ⟨hnN,hn2,?_,?_,hcomp⟩
      · calc
          (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^δ * Nat.maxPrimeFac (n+1) := hcomp.1
          _ ≤ (N : ℝ)^δ * (N : ℝ)^(1/2-2*τ) := mul_le_mul_of_nonneg_left hlo.le hdpos.le
          _ = (N : ℝ)^(δ+(1/2-2*τ)) := (Real.rpow_add hn0 _ _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      · exact hlo.le.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    · by_cases hhi : (N : ℝ)^(1/2+2*τ) < (Nat.maxPrimeFac (n+1) : ℝ)
      · apply mem_union_right
        apply mem_filter.mpr
        refine ⟨hnN,hn2,?_,?_,hcomp⟩
        · apply (mul_le_mul_iff_left₀ hdpos).mp
          calc
            (N : ℝ)^(1/2+τ) * (N : ℝ)^δ = (N : ℝ)^((1/2+τ)+δ) :=
              (Real.rpow_add hn0 _ _).symm
            _ ≤ (N : ℝ)^(1/2+2*τ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
            _ ≤ (Nat.maxPrimeFac (n+1) : ℝ) := hhi.le
            _ ≤ (Nat.maxPrimeFac n : ℝ) * (N : ℝ)^δ := by simpa only [mul_comm] using hcomp.2
        · exact (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)).trans hhi.le
      · apply mem_union_left
        apply mem_union_right
        apply mem_filter.mpr
        refine ⟨hnN,Nat.maxPrimeFac (n+1),?_,le_of_not_gt hlo,le_of_not_gt hhi,Nat.maxPrimeFac_dvd⟩
        exact Nat.mem_primesBelow.mpr ⟨Nat.maxPrimeFac_le.trans_lt (by omega),
          Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)⟩
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_range.mpr (by omega))))

lemma logRatioSet_card_le_ranges (N : ℕ) (τ δ : ℝ)
    (hN : 1 < N) (hτ : 0 ≤ τ) (hδ : δ ≤ τ) :
    (logRatioSet N δ).card ≤ 2 + (lowLogRatioSet N (1/2-τ) δ).card +
      (primeDivisorBandSet N (1/2-2*τ) (1/2+2*τ)).card + (highLogRatioSet N (1/2+τ) δ).card := by
  have hc := card_le_card (logRatioSet_subset_ranges N τ δ hN hτ hδ)
  have h1 := card_union_le (range 2) (lowLogRatioSet N (1/2-τ) δ)
  have h2 := card_union_le (range 2 ∪ lowLogRatioSet N (1/2-τ) δ)
    (primeDivisorBandSet N (1/2-2*τ) (1/2+2*τ))
  have h3 := card_union_le (range 2 ∪ lowLogRatioSet N (1/2-τ) δ ∪
    primeDivisorBandSet N (1/2-2*τ) (1/2+2*τ)) (highLogRatioSet N (1/2+τ) δ)
  rw [card_range] at h1
  omega

lemma logRatioSet_eventually_le (a τ δ : ℝ)
    (ha : 0 < a) (hτ : 0 < τ) (hτsmall : τ ≤ 1/8)
    (hδ : 0 ≤ δ) (hδa : δ ≤ a/2) (hδτ : δ ≤ τ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((logRatioSet N δ).card : ℝ)/N ≤
      320*a^2 + 64*δ/a + 32*τ/(1/2-2*τ) +
        (8*Real.exp 19*(1/2-τ)/(τ/64)^2)*δ + ε := by
  have hl := lowLogRatioSet_eventually_le (1/2-τ) a δ (by linarith) ha hδ hδa (ε/4) (by positivity)
  have hb := primeDivisorBandSet_eventually_le (1/2-2*τ) (1/2+2*τ)
    (by linarith) (by linarith) (ε/4) (by positivity)
  have hh := highLogRatioSet_eventually_le (1/2+τ) δ (τ/64)
    (by linarith) hδ (by positivity) (by linarith) (ε/4) (by positivity)
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hl,hb,hh,h2.eventually_lt_const (by positivity : (0 : ℝ) < ε/4),
    eventually_gt_atTop (1 : ℕ)] with N hl hb hh h2 hN
  have hc := (Nat.cast_le (α := ℝ)).mpr (logRatioSet_card_le_ranges N τ δ hN hτ.le hδτ)
  push_cast at hc
  have hc' := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  simp only [add_div] at hc'
  have eb : 8*((1/2+2*τ)-(1/2-2*τ))/(1/2-2*τ)=32*τ/(1/2-2*τ) := by ring
  have eh : 1-(1/2+τ)=1/2-τ := by ring
  rw [eb] at hb
  rw [eh] at hh
  linarith

/-- Logarithmic near-ties occupy arbitrarily small upper proportions when
the width is chosen sufficiently small. -/
theorem logRatioSet_uniform_rarity (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ((logRatioSet N δ).card : ℝ)/N ≤ ε := by
  let a := min 1 (ε/2560)
  let τ := min (1/8) (ε/1024)
  let K := 8*Real.exp 19*(1/2-τ)/(τ/64)^2
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haε : a ≤ ε/2560 := min_le_right _ _
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1/8 := min_le_left _ _
  have hτε : τ ≤ ε/1024 := min_le_right _ _
  have hK : 0 ≤ K := by
    dsimp only [K]
    have : 0 ≤ 1/2-τ := by linarith
    positivity
  have hB : 0 < 64/a+K+1 := by positivity
  let δ := min (a/2) (min τ (ε/(8*(64/a+K+1))))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min hτ (by positivity))
  have hδa : δ ≤ a/2 := min_le_left _ _
  have hδτ : δ ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/(8*(64/a+K+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hfirst : 320*a^2 ≤ ε/8 := by nlinarith
  have hband : 32*τ/(1/2-2*τ) ≤ ε/8 := by
    have hden : 0 < 1/2-2*τ := by linarith
    calc
      _ ≤ 128*τ := (div_le_iff₀ hden).mpr (by nlinarith)
      _ ≤ _ := by linarith
  have hwidth : 64*δ/a+K*δ ≤ ε/8 := by
    have h := (le_div_iff₀ (show 0 < 8*(64/a+K+1) by positivity)).mp hδε
    have he : δ*(8*(64/a+K+1))=8*(64*δ/a+K*δ)+8*δ := by ring
    rw [he] at h
    linarith
  refine ⟨δ,hδ,?_⟩
  filter_upwards [logRatioSet_eventually_le a τ δ ha hτ hτ1 hδ.le hδa hδτ (ε/2) (by positivity)]
    with N hN
  change _ ≤ 320*a^2+64*δ/a+32*τ/(1/2-2*τ)+K*δ+ε/2 at hN
  linarith

#print axioms logRatioSet_uniform_rarity
end FiniteSieve
end Erdos371
