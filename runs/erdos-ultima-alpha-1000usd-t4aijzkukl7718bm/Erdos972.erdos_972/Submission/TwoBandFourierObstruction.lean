import Submission.MidpointFourierScales
import Submission.FullRowFourFactorReduction
import Submission.LowFloorFourierScales

/-! Simultaneous removal of fixed bands around zero and the midpoint in the
exact Fourier covariance. This leaves an explicit, uncontrolled complement. -/
namespace Erdos972TwoBandFourierObstruction

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972LowFloorFourierScales
open Erdos972MidpointFourierBounds Erdos972MidpointFourierScales
open Erdos972DivisorMeanRecenter Erdos972FullRowFourFactorReduction
open Erdos972FullRecenterCovarianceScales Erdos972GrowingTypeIIReduction
open Erdos972CenteredRowScales Erdos972CommonCovarianceScales Erdos972Topology

set_option maxHeartbeats 2000000

lemma image_norm_sum_bound {ι κ : Type*} [DecidableEq κ] (S : Finset ι)
    (g : ι → κ) (f : κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ j ∈ S, ‖f (g j)‖ ≤ B/(S.card+1)) :
    (∑ k ∈ S.image g, ‖f k‖) ≤ B := by
  apply (sum_image_le_of_nonneg (fun k hk => norm_nonneg (f k))).trans
  have hh := sum_le_sum hf
  simp only [sum_const, nsmul_eq_mul] at hh
  have hs : (S.card : ℝ)/(S.card+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right hs hB
  have he : (S.card : ℝ)*(B/(S.card+1)) = (S.card : ℝ)/(S.card+1)*B := by ring
  rw [he] at hh
  linarith only [hh, hm]

lemma union_norm_sum_bound {κ : Type*} [DecidableEq κ] (A B : Finset κ)
    (f : κ → ℂ) {E F : ℝ} (hA : (∑ k ∈ A, ‖f k‖) ≤ E)
    (hB : (∑ k ∈ B, ‖f k‖) ≤ F) : (∑ k ∈ A ∪ B, ‖f k‖) ≤ E+F := by
  have he := sum_union_inter (s₁ := A) (s₂ := B) (f := fun k => ‖f k‖)
  have hn : 0 ≤ ∑ k ∈ A ∩ B, ‖f k‖ := sum_nonneg (fun k hk => norm_nonneg _)
  linarith only [he, hn, hA, hB]

noncomputable def twoBands (J : ℕ) [NeZero J] (S T : Finset ℤ) : Finset (ZMod J) :=
  S.image (fun k : ℤ => (k : ZMod J)) ∪
    T.image (fun k : ℤ => (midpointFrequency J k : ZMod J))

/-- Both bands are controlled at a single scale. The proof bounds absolute
mode sums, so overlap and possible cancellations between modes cause no gap. -/
theorem eventually_two_bands_small {α : ℝ} (hα : 1 ≤ α) (S T : Finset ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, FullTwoSidedScale α u →
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (twoBands (floorMul α (scaleCutoff α u)+1) S T)| ≤ ε*(scaleCutoff α u : ℝ) := by
  have hδS : 0 < ε/(2*(S.card+1)) := by positivity
  have hδT : 0 < ε/(2*(T.card+1)) := by positivity
  have hs := (eventually_all_finset S).mpr (fun k hk => eventually_fourier_term_small hα k hδS)
  have ht := (eventually_all_finset T).mpr (fun k hk => eventually_midpoint_term_small hα k hδT)
  filter_upwards [hs, ht] with u huS huT
  intro hrows
  let N := scaleCutoff α u
  let J := floorMul α N+1
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let F := fun k : ZMod J => covarianceFourierTerm α N R R k/(J : ℂ)
  have hJ : (0 : ℝ) < J := by dsimp only [J]; positivity
  have hS : (∑ k ∈ S.image (fun k : ℤ => (k : ZMod J)), ‖F k‖) ≤ ε/2*(N : ℝ) := by
    apply image_norm_sum_bound S _ F (by positivity)
    intro k hk
    dsimp only [F]
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hJ).mpr
    have hh := huS k hk
    change ‖covarianceFourierTerm α N R R (k : ZMod J)‖ ≤
      ε/(2*(S.card+1))*(J : ℝ)*(N : ℝ) at hh
    exact hh.trans_eq (by rw [div_mul_eq_div_div]; ring)
  have hT : (∑ k ∈ T.image (fun k : ℤ => (midpointFrequency J k : ZMod J)), ‖F k‖) ≤ ε/2*(N : ℝ) := by
    apply image_norm_sum_bound T _ F (by positivity)
    intro k hk
    exact (huT k hk hrows).trans_eq (by dsimp only [N]; rw [div_mul_eq_div_div]; ring)
  have hh := union_norm_sum_bound _ _ F hS hT
  change |frequencyCovariance α N R R (twoBands J S T)| ≤ ε*(N : ℝ)
  unfold frequencyCovariance
  rw [sum_div]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ twoBands J S T, ‖F k‖) ≤ _
  dsimp only [twoBands]
  linarith only [hh]

/-- A counterexample forces a near -N contribution outside BOTH fixed bands,
with the original, dual and joint rows all belonging to that same scale. -/
theorem finite_primeSet_forces_negative_two_band_complement {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hfin : (primeSet α).Finite)
    (S T : Finset ℤ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < growingCutoff u ∧ 0 < scaleCutoff α u ∧
      OutputPrimeScale α u ∧ FullTwoSidedScale α u ∧
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (twoBands (floorMul α (scaleCutoff α u)+1) S T)ᶜ /
          (scaleCutoff α u : ℝ)+1| ≤ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_two_bands_small hα.le S T (show 0 < ε/2 by positivity))
  obtain ⟨u, N, hu, rfl, hcut, hN, hrows, hfullrows, hfull⟩ :=
    finite_primeSet_forces_negative_recentered_fourFactor_full hα hI hfin
      (show 0 < ε/2 by positivity) (max B K)
  have hlow := hK u ((le_max_right B K).trans hu.le) hfullrows
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let A := twoBands (floorMul α (scaleCutoff α u)+1) S T
  have hs := recentered_fourFactor_frequency_split hα.le (scaleCutoff α u)
    (growingCutoff u) (growingCutoff u) (growingCutoff u) (growingCutoff u) A
  have hl : |frequencyCovariance α (scaleCutoff α u) R R A/(scaleCutoff α u : ℝ)| ≤ ε/2 := by
    rw [abs_div, abs_of_pos hNR]
    exact (div_le_iff₀ hNR).mpr hlow
  refine ⟨u, (le_max_left B K).trans_lt hu, (le_max_left B K).trans_lt hcut,
    hN, hrows, hfullrows, ?_⟩
  have he : frequencyCovariance α (scaleCutoff α u) R R Aᶜ/(scaleCutoff α u : ℝ)+1 =
      (meanCenteredFourFactor α (scaleCutoff α u) (growingCutoff u) (growingCutoff u)
        (growingCutoff u) (growingCutoff u)/(scaleCutoff α u : ℝ)+1)-
      frequencyCovariance α (scaleCutoff α u) R R A/(scaleCutoff α u : ℝ) := by
    rw [hs]
    ring
  change |frequencyCovariance α (scaleCutoff α u) R R Aᶜ/(scaleCutoff α u : ℝ)+1| ≤ ε
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hfull, hl])

#print axioms eventually_two_bands_small
#print axioms finite_primeSet_forces_negative_two_band_complement

end Erdos972TwoBandFourierObstruction
