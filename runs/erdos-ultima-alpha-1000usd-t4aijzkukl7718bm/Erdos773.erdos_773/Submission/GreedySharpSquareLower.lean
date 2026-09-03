import Submission.GreedySharpSquareScales

/-!
An improved explicit coefficient for the actual square-Sidon N^(2/3) lower
bound. This remains below the unit coefficient needed at epsilon=1/3.
-/
namespace Erdos773.GreedySharpSquareLower
open Finset Filter SquareCollisionCodegrees GreedySquareScales GreedyGrowingSquareScales
open GreedyTightSquareScales GreedySharpSquareScales
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
noncomputable section

/-- The proved collision coefficient improves the actual square-Sidon lower
    coefficient to 1/1200. No increase in the exponent is claimed. -/
theorem eventual_power_lower : ∀ᶠ N : ℕ in atTop,
    (1/1200:ℝ)*(N:ℝ)^(2/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  obtain ⟨M,hcert⟩ := eventually_atTop.mp
    (GreedyGrowingSquareCertificate.eventually_certificate 97)
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heighth : Tendsto (fun N : ℕ => (N:ℝ)^(1/8:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/776)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ) < 1)
  filter_upwards [ControlledSquareSampling.logarithmic_sampling (1/1000) (by norm_num),
    eventually_pair_codegree_bound (1/16) (by norm_num),hlog.eventually_ge_atTop 1000000000000,
    heighth.eventually_ge_atTop 4,hsmall,eventually_ge_atTop 1,eventually_ge_atTop ((max M 1001)^97)]
    with N hsample hcodeg hL hlarge hsmall hN hNM
  have hX : (0:ℝ) < N := by exact_mod_cast hN
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hLpos : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs : Real.log (N:ℝ) ≤ (N:ℝ)^(1/776:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hLpos.le,
      abs_of_nonneg (Real.rpow_nonneg hX.le (1/776:ℝ)),one_mul] using hsmall
  have hlogSquare : (Real.log (N:ℝ))^2 ≤ (N:ℝ)^(1/388:ℝ) := by
    have hh := pow_le_pow_left₀ hLpos.le hs 2
    have he : ((N:ℝ)^(1/776:ℝ))^2 = (N:ℝ)^(1/388:ℝ) := by
      rw [← Real.rpow_mul_natCast hX.le]
      norm_num
    rwa [he] at hh
  have hlogOld : (Real.log (N:ℝ))^2 ≤ (N:ℝ)^(1/8:ℝ) :=
    hlogSquare.trans (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1/388:ℝ) ≤ 1/8))
  obtain ⟨hp,hp1,hμ,hdegree,hKsq⟩ := GreedySharpSquareScales.scalar_bounds hX1 hLpos hlogOld hlarge
  let m := sharpRoot24 (N:ℝ) (Real.log N)
  have hvolume : (N:ℝ) ≤ (m:ℝ)^97 := GreedySharpSquareScales.volume97 hX1 hLpos hlogSquare
  have hvolumeNat : N ≤ m^97 := by exact_mod_cast hvolume
  have hmmax : max M 1001 ≤ m :=
    (Nat.pow_le_pow_iff_left (by omega : (97:ℕ) ≠ 0)).mp (hNM.trans hvolumeNat)
  have hmM : M ≤ m := (le_max_left _ _).trans hmmax
  have hm1001 : 1001 ≤ m := (le_max_right _ _).trans hmmax
  have hmpos : 0 < m := by omega
  have hupper := sharp_degree hX hLpos hm1001
  obtain ⟨A,hAN,hAP,hsize,hAupper,hE⟩ := hsample
  norm_num at hsize hE
  have hsize' : (20/21:ℝ)*(N:ℝ)/Real.log N ≤ (A.card:ℝ) := by
    apply le_trans _ hsize
    apply div_le_div_of_nonneg_right _ hLpos.le
    exact mul_le_mul_of_nonneg_right (by norm_num : (20/21:ℝ) ≤ 999/1000) hX.le
  have hAupper' : (A.card:ℝ) ≤ N := by
    exact_mod_cast (show A.card ≤ N by simpa using card_le_card hAN)
  have hK : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((pairEdges A a b).card:ℝ) ≤ (N:ℝ)^(1/16:ℝ) := by
    intro a ha b hb hab
    have hmono : ((pairEdges A a b).card:ℝ) ≤ ((pairEdges (Icc 1 N) a b).card:ℝ) := by
      exact_mod_cast card_le_card (pairEdges_mono hAN a b)
    exact hmono.trans (hcodeg a (hAN ha) b (hAN hb) hab)
  have hoverlap := overlap_cost hX (Nat.cast_nonneg A.card) hAupper' hKsq
  have hedges := GreedySharpSquareScales.retained_edge_cost hX hLpos hsize hE
  have hτ : 1 ≤ tightHorizon (Real.log (N:ℝ)) := by
    linarith only [tightHorizon_hundred hL]
  have hbudget := tightHorizon_budget hX hL hvolume
  have hM := hcert m hmM (tightHorizon (Real.log (N:ℝ))) hτ hbudget N A hAN hvolume hAP ((N:ℝ)^(1/16:ℝ)) hK
    (probability N) (sharpWeight N (Real.log N)) hp hp1 hμ hdegree hoverlap hedges
  exact sharp_scale_lower hX hLpos hmpos hsize' hupper hM

#print axioms eventual_power_lower
end
end Erdos773.GreedySharpSquareLower
