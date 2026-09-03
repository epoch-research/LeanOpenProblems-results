import Submission.GreedySquareScales

/-!
An actual improvement of the square-Sidon lower bound: every fixed positive
multiple of N/(N log N)^(1/3) is eventually attained. The logarithmic loss
is not removed, and this theorem does not settle the near-linear conjecture.
-/
namespace Erdos773.GreedySquareSidonLower
open Finset Filter SquareCollisionCodegrees GreedySquareScales
set_option maxHeartbeats 2500000
noncomputable section

/-- The leading multiplier at the existing logarithmic-loss scale is
    unbounded. This is an unconditional statement about the actual maximum
    Sidon-subset cardinality among the first N positive squares. -/
theorem eventual_log_lower (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ N : ℕ in atTop,
    c*(N:ℝ)/((N:ℝ)*Real.log N)^(1/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  obtain ⟨M,hcert⟩ := eventually_atTop.mp
    (GreedySquareCertificate.eventually_certificate 96 (1024*c) (by positivity))
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heighth : Tendsto (fun N : ℕ => (N:ℝ)^(1/8:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/16)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ) < 1)
  filter_upwards [ControlledSquareSampling.logarithmic_sampling (1/2) (by norm_num),
    eventually_pair_codegree_bound (1/16) (by norm_num),hlog.eventually_ge_atTop 1,
    heighth.eventually_ge_atTop 4,hsmall,eventually_ge_atTop 1,eventually_ge_atTop (M^96)]
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
  obtain ⟨hp,hp1,hμ,hdegree,hvolume,hupper,hKsq⟩ := scalar_bounds hX1 hLpos hlogSquare hlarge
  let m := degreeRoot (N:ℝ) (Real.log N)
  have hvolumeNat : N ≤ m^96 := by exact_mod_cast hvolume
  have hmM : M ≤ m := (Nat.pow_le_pow_iff_left (by omega : (96:ℕ) ≠ 0)).mp (hNM.trans hvolumeNat)
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
  have hM := hcert m hmM N A hAN hvolume hAP ((N:ℝ)^(1/16:ℝ)) hK
    (probability N) (penaltyWeight N (Real.log N)) hp hp1 hμ hdegree hoverlap hedges
  exact scale_lower hX hLpos hmpos hc hsize' hupper hM

/-- Equivalently, the actual square-Sidon maximum divided by the old
    logarithmic-loss scale tends to infinity. -/
theorem normalized_max_tendsto :
    Tendsto (fun N : ℕ =>
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ)*
        ((N:ℝ)*Real.log N)^(1/3:ℝ)/(N:ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventual_log_lower (max 0 b) (le_max_left _ _),
    eventually_ge_atTop 1,hlog.eventually_ge_atTop 1] with N hN hN1 hL
  have hX : (0:ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hR : 0 < ((N:ℝ)*Real.log N)^(1/3:ℝ) := Real.rpow_pos_of_pos (mul_pos hX hL0) _
  have hh := (div_le_iff₀ hR).mp hN
  apply (le_div_iff₀ hX).mpr
  exact (mul_le_mul_of_nonneg_right (le_max_right 0 b) hX.le).trans hh

#print axioms eventual_log_lower
#print axioms normalized_max_tendsto
end
end Erdos773.GreedySquareSidonLower
