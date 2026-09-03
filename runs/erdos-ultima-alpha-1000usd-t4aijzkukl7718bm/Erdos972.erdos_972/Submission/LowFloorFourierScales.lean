import Submission.FiniteFloorFourierBounds

/-! Actual low-frequency smallness in the exact finite Fourier expansion.
This is uniform on every sufficiently large scale for each fixed finite set
of integer frequencies. It does not control the complementary frequencies. -/
namespace Erdos972LowFloorFourierScales

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972FloorCovarianceFourier Erdos972FiniteFloorFourierBounds
open Erdos972DivisorMeanRecenter Erdos972RecenteredRemainderPrefix
open Erdos972RecenteredPrefixScales Erdos972CovarianceScaleBudgets
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales

set_option maxHeartbeats 1500000

lemma meanCenteredTypeII_one (U V : ℕ) : meanCenteredTypeII U V 1 = 0 := by
  simp [meanCenteredTypeII, ArithmeticFunction.mul_apply, Erdos972Vaughan.tail, Erdos972Vaughan.cutoff]

/-- Every fixed integer Fourier mode is o(N) after the Fourier normalization.
The bound is for the genuine recentered arithmetic functions. -/
theorem eventually_fourier_term_small {α : ℝ} (hα : 1 ≤ α) (k : ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      ‖covarianceFourierTerm α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (k : ZMod (floorMul α (scaleCutoff α u)+1))‖ ≤
          ε*(floorMul α (scaleCutoff α u)+1 : ℕ)*(scaleCutoff α u : ℝ) := by
  let C : ℝ := 2+2*Real.pi*|(k : ℝ)|
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC2 : 0 < C^2 := sq_pos_of_pos hC
  filter_upwards [eventually_centered_remainder_prefix hα (show 0 < ε/C^2 by positivity),
    eventually_recentered_prefix_model hα (show (0 : ℝ) < 1 by norm_num),
    (scaleCutoff_tendsto hα).eventually_ge_atTop 1] with u hin hout hN
  let N := scaleCutoff α u
  let M := floorMul α N
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let ρ := 1-recenteredConstant (growingCutoff u) (growingCutoff u)
  have hNM : N ≤ M := self_le_floorMul hα N
  have hM : 0 < M := hN.trans hNM
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hrho : |ρ| ≤ (N : ℝ) := by
    have hh := hout 1 hM
    simpa only [total, show (Ioc 0 1 : Finset ℕ) = {1} by decide, sum_singleton, meanCenteredTypeII_one,
      zero_sub, abs_neg, Nat.cast_one, mul_one, one_mul, ρ, N, R] using hh
  have hout' : ∀ X ≤ M, |total X R-ρ*X| ≤ (N : ℝ) := by
    intro X hX
    simpa only [one_mul] using hout X hX
  by_cases hk : (k : ZMod (M+1)) = 0
  · change ‖covarianceFourierTerm α N R R (k : ZMod (M+1))‖ ≤ _
    rw [hk, covarianceFourierTerm_zero, norm_zero]
    positivity
  have hB := output_dft_prefix_bound hM R (by simp [R]) hrho hout' k hk
  have hA := input_floor_transform_prefix_bound hα hN R
    (hin N le_rfl hNM) k
  have hA' : ‖centeredFloorTransform α N R (k : ZMod (M+1))‖ ≤ C*(ε/C^2*(N : ℝ)) := by
    apply hA.trans
    have hc : 1+2*Real.pi*|(k : ℝ)| ≤ C := by dsimp only [C]; linarith
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hprod := mul_le_mul hA' hB (norm_nonneg _)
    (show 0 ≤ C*(ε/C^2*(N : ℝ)) by positivity)
  change ‖covarianceFourierTerm α N R R (k : ZMod (M+1))‖ ≤ ε*(M+1 : ℕ)*(N : ℝ)
  rw [covarianceFourierTerm, norm_mul]
  apply hprod.trans
  change C*(ε/C^2*(N : ℝ))*(C*(N : ℝ)) ≤ ε*(M+1 : ℕ)*(N : ℝ)
  have he : C*(ε/C^2*(N : ℝ))*(C*(N : ℝ)) = ε*(N : ℝ)^2 := by field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hNM.trans (Nat.le_succ M)))
    (show 0 ≤ ε*(N : ℝ) by positivity)
  nlinarith only [hh]

/-- A finite set of integer frequencies is mapped into the varying modulus.
Possible collisions are harmless; no injectivity assumption is made. -/
theorem eventually_low_frequency_covariance_small {α : ℝ} (hα : 1 ≤ α)
    (S : Finset ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      |frequencyCovariance α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (S.image (fun k : ℤ => (k : ZMod (floorMul α (scaleCutoff α u)+1))))| ≤
          ε*(scaleCutoff α u : ℝ) := by
  have hevent : ∀ᶠ u : ℕ in atTop, ∀ k ∈ S,
      ‖covarianceFourierTerm α (scaleCutoff α u)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)
        (k : ZMod (floorMul α (scaleCutoff α u)+1))‖ ≤
          (ε/(S.card+1))*(floorMul α (scaleCutoff α u)+1 : ℕ)*(scaleCutoff α u : ℝ) := by
    exact (eventually_all_finset S).mpr (fun k hk => eventually_fourier_term_small hα k (by positivity))
  filter_upwards [hevent] with u hu
  let N := scaleCutoff α u
  let J := floorMul α N+1
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let K := S.image (fun k : ℤ => (k : ZMod J))
  have hJ : (0 : ℝ) < J := by dsimp only [J]; positivity
  have hsum : ‖∑ k ∈ K, covarianceFourierTerm α N R R k‖ ≤
      (S.card : ℝ)*(ε/(S.card+1)*(J : ℝ)*(N : ℝ)) := by
    apply (norm_sum_le _ _).trans
    apply (sum_image_le_of_nonneg (fun k hk => norm_nonneg (covarianceFourierTerm α N R R k))).trans
    exact (sum_le_sum hu).trans_eq (by simp only [sum_const, nsmul_eq_mul]; rfl)
  have hcard : (S.card : ℝ)/(S.card+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hsum' : ‖∑ k ∈ K, covarianceFourierTerm α N R R k‖ ≤ ε*(J : ℝ)*(N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ ε*(J : ℝ)*(N : ℝ) by positivity)
    have heq : (S.card : ℝ)*(ε/(S.card+1)*(J : ℝ)*(N : ℝ)) =
        (S.card : ℝ)/(S.card+1)*(ε*(J : ℝ)*(N : ℝ)) := by ring
    rw [heq] at hsum
    linarith only [hsum, hh]
  change |frequencyCovariance α N R R K| ≤ ε*(N : ℝ)
  unfold frequencyCovariance
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hJ).mpr
  nlinarith only [hsum']

#print axioms eventually_fourier_term_small
#print axioms eventually_low_frequency_covariance_small

end Erdos972LowFloorFourierScales
