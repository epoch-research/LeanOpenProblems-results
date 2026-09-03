import Submission.GreedyGrowingSquareScales

/-!
A square-Sidon lower bound of order N^(2/3), with no logarithmic loss.
The constant is explicit and positive. This does not reach the conjectured
near-linear exponent, or the exact unit-constant epsilon=1/3 statement.
-/
namespace Erdos773.GreedySquarePowerLower
open Finset Filter SquareCollisionCodegrees GreedySquareScales GreedyGrowingSquareScales
set_option maxHeartbeats 2500000
noncomputable section

/-- An actual N^(2/3) lower bound, after every sampling, linearization,
    regularization, rounding, and growing-horizon loss has been included. -/
theorem eventual_power_lower : ∀ᶠ N : ℕ in atTop,
    lowerConstant*(N:ℝ)^(2/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  obtain ⟨M,hcert⟩ := eventually_atTop.mp
    (GreedyGrowingSquareCertificate.eventually_certificate 192)
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heighth : Tendsto (fun N : ℕ => (N:ℝ)^(1/8:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/16)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ) < 1)
  filter_upwards [ControlledSquareSampling.logarithmic_sampling (1/2) (by norm_num),
    eventually_pair_codegree_bound (1/16) (by norm_num),hlog.eventually_ge_atTop 15360000,
    heighth.eventually_ge_atTop 4,hsmall,eventually_ge_atTop 1,eventually_ge_atTop (M^192)]
    with N hsample hcodeg hL hlarge hsmall hN hNM
  have hX : (0:ℝ) < N := by exact_mod_cast hN
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hLpos : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs : Real.log (N:ℝ) ≤ (N:ℝ)^(1/16:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hLpos.le,
      abs_of_nonneg (Real.rpow_nonneg hX.le (1/16:ℝ)),one_mul] using hsmall
  have hlogSquare : (Real.log (N:ℝ))^2 ≤ (N:ℝ)^(1/8:ℝ) := by
    have hh := pow_le_pow_left₀ hLpos.le hs 2
    rw [(eighth_identities hX.le).2.2] at hh
    exact hh
  obtain ⟨hp,hp1,hμ,hdegree,hvolume,hupper,hKsq⟩ := scalar24_bounds hX1 hLpos hlogSquare hlarge
  let m := degreeRoot24 (N:ℝ) (Real.log N)
  have hvolumeNat : N ≤ m^192 := by exact_mod_cast hvolume
  have hmM : M ≤ m := (Nat.pow_le_pow_iff_left (by omega : (192:ℕ) ≠ 0)).mp (hNM.trans hvolumeNat)
  have hmpos : 0 < m := by
    by_contra! hn
    have hmzero : m = 0 := by omega
    rw [hmzero] at hvolumeNat
    norm_num at hvolumeNat
    omega
  obtain ⟨A,hAN,hAP,hsize,hAupper,hE⟩ := hsample
  have hsize' : (N:ℝ)/(2*Real.log N) ≤ (A.card:ℝ) := by
    convert hsize using 1; ring
  have hE' : ((edges A).card:ℝ) ≤ (N:ℝ)^2/(Real.log N)^3 := by
    apply hE.trans
    apply div_le_div_of_nonneg_right _ (pow_nonneg hLpos.le 3)
    exact mul_le_of_le_one_left (sq_nonneg (N:ℝ)) (by norm_num)
  have hAupper' : (A.card:ℝ) ≤ N := by
    exact_mod_cast (show A.card ≤ N by simpa using card_le_card hAN)
  have hK : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((pairEdges A a b).card:ℝ) ≤ (N:ℝ)^(1/16:ℝ) := by
    intro a ha b hb hab
    have hmono : ((pairEdges A a b).card:ℝ) ≤ ((pairEdges (Icc 1 N) a b).card:ℝ) := by
      exact_mod_cast card_le_card (pairEdges_mono hAN a b)
    exact hmono.trans (hcodeg a (hAN ha) b (hAN hb) hab)
  have hoverlap := overlap_cost hX (Nat.cast_nonneg A.card) hAupper' hKsq
  have hedges := retained_edge_cost hX hLpos hsize' hE'
  have hτ := horizon_one hL
  have hbudget := horizon_budget hX hL hvolume
  have hM := hcert m hmM (horizon (Real.log (N:ℝ))) hτ hbudget N A hAN hvolume hAP ((N:ℝ)^(1/16:ℝ)) hK
    (probability N) (penaltyWeight N (Real.log N)) hp hp1 hμ hdegree hoverlap hedges
  have hτ0 : 0 ≤ horizon (Real.log (N:ℝ)) := by linarith only [hτ]
  have hfinal := GreedyGrowingSquareScales.scale_lower hX hLpos hmpos hτ0 hsize' hupper hM
  rw [lower_identity hX hLpos] at hfinal
  exact hfinal

lemma rational_le_constant : (1/10000000:ℝ) ≤ lowerConstant := by
  have hrootpos : 0 < (15360000:ℝ)^(1/3:ℝ) := by positivity
  have hcube : ((15360000:ℝ)^(1/3:ℝ))^3 = 15360000 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 15360000)]
    norm_num
  have hroot : (15360000:ℝ)^(1/3:ℝ) ≤ 256 := by
    apply le_of_pow_le_pow_left₀ (by omega : (3:ℕ) ≠ 0) (by norm_num : (0:ℝ) ≤ 256)
    rw [hcube]
    norm_num
  have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : (0:ℝ) < 32768*(15360000:ℝ)^(1/3:ℝ))
    (mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 32768))
  unfold lowerConstant
  exact (by norm_num : (1/10000000:ℝ) ≤ 1/(32768*256)).trans hh

/-- A simple rational version of the new power-scale lower bound. -/
theorem eventual_rational_power_lower : ∀ᶠ N : ℕ in atTop,
    (1/10000000:ℝ)*(N:ℝ)^(2/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  filter_upwards [eventual_power_lower] with N hN
  exact (mul_le_mul_of_nonneg_right rational_le_constant
    (Real.rpow_nonneg (Nat.cast_nonneg N) (2/3:ℝ))).trans hN

#print axioms eventual_power_lower
#print axioms rational_le_constant
#print axioms eventual_rational_power_lower
end
end Erdos773.GreedySquarePowerLower
