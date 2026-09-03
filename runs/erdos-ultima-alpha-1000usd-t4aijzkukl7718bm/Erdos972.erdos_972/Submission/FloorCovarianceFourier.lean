import Submission.RecenterFourFactorReduction

/-! Exact finite Fourier formulas for the floor covariance. These retain the
floor phase and the mean term, and assert no high-frequency cancellation. -/
namespace Erdos972FloorCovarianceFourier

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972DivisorMeanRecenter

set_option maxHeartbeats 1500000

/-- Fourier inversion tested against an arbitrary finite weighted sample.
The sampling map need not be injective. -/
lemma sample_fourier_inversion {J : ℕ} [NeZero J] {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (g : ι → ZMod J) (b : ZMod J → ℂ) :
    (∑ n ∈ s, a n*b (g n)) =
      (∑ k : ZMod J, (∑ n ∈ s, a n*ZMod.stdAddChar (k*g n))*ZMod.dft b k)/(J : ℂ) := by
  have hinv (j : ZMod J) : b j =
      (J : ℂ)⁻¹*(∑ k : ZMod J, ZMod.stdAddChar (k*j)*ZMod.dft b k) := by
    have hh := congrFun (ZMod.dft.symm_apply_apply b) j
    rw [ZMod.invDFT_apply] at hh
    simpa only [smul_eq_mul] using hh.symm
  calc
    _ = ∑ n ∈ s, a n*((J : ℂ)⁻¹*∑ k : ZMod J, ZMod.stdAddChar (k*g n)*ZMod.dft b k) := by
      apply sum_congr rfl
      intro n hn
      rw [← hinv]
    _ = (J : ℂ)⁻¹ * ∑ n ∈ s, ∑ k : ZMod J, (a n*ZMod.stdAddChar (k*g n))*ZMod.dft b k := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [sum_comm]
      simp only [sum_mul, mul_sum, div_eq_mul_inv]
      ring

lemma covariance_eq_centered_sum (N : ℕ) (f g : ℕ → ℝ) :
    covariance N f g = ∑ n ∈ Ioc 0 N, (f n-total N f/N)*g n := by
  simp only [covariance, total, sub_mul, sum_sub_distrib, ← mul_sum]
  ring

lemma centered_total_zero (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, (f n-total N f/N)) = 0 := by
  by_cases hN : N = 0
  · simp [hN]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  change total N f-(N : ℝ)*(total N f/N) = 0
  field_simp
  ring

noncomputable def outputLift (M : ℕ) (f : ℕ → ℝ) (j : ZMod (M+1)) : ℂ := f j.val

noncomputable def centeredFloorTransform (α : ℝ) (N : ℕ) (f : ℕ → ℝ)
    (k : ZMod (floorMul α N+1)) : ℂ :=
  ∑ n ∈ Ioc 0 N, ((f n-total N f/N : ℝ) : ℂ)*
    ZMod.stdAddChar (k*(floorMul α n : ZMod (floorMul α N+1)))

noncomputable def covarianceFourierTerm (α : ℝ) (N : ℕ) (f g : ℕ → ℝ)
    (k : ZMod (floorMul α N+1)) : ℂ :=
  centeredFloorTransform α N f k * ZMod.dft (outputLift (floorMul α N) g) k

/-- Exact inversion with modulus one larger than the largest output.
There is no wrapping error, no smoothing error and no discarded mean term. -/
theorem floor_covariance_fourier {α : ℝ} (hα : 1 ≤ α) (N : ℕ) (f g : ℕ → ℝ) :
    (covariance N f (fun n => g (floorMul α n)) : ℂ) =
      (∑ k : ZMod (floorMul α N+1), covarianceFourierTerm α N f g k)/
        ((floorMul α N+1 : ℕ) : ℂ) := by
  have hh := sample_fourier_inversion (Ioc 0 N)
    (fun n => ((f n-total N f/N : ℝ) : ℂ))
    (fun n => (floorMul α n : ZMod (floorMul α N+1)))
    (outputLift (floorMul α N) g)
  rw [covariance_eq_centered_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, covarianceFourierTerm, centeredFloorTransform]
  rw [← hh]
  apply sum_congr rfl
  intro n hn
  have hgn : floorMul α n < floorMul α N+1 := Nat.lt_succ_of_le
    ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2)
  simp only [outputLift, ZMod.val_natCast_of_lt hgn]

lemma centeredFloorTransform_zero (α : ℝ) (N : ℕ) (f : ℕ → ℝ) :
    centeredFloorTransform α N f 0 = 0 := by
  simp only [centeredFloorTransform, zero_mul, AddChar.map_zero_eq_one, mul_one]
  rw [← Complex.ofReal_sum, centered_total_zero, Complex.ofReal_zero]

lemma covarianceFourierTerm_zero (α : ℝ) (N : ℕ) (f g : ℕ → ℝ) :
    covarianceFourierTerm α N f g 0 = 0 := by
  rw [covarianceFourierTerm, centeredFloorTransform_zero, zero_mul]

/-- The zero mode vanishes because the input is centered, not because the
uncentered arithmetic remainder has zero mean. -/
theorem floor_covariance_fourier_nonzero {α : ℝ} (hα : 1 ≤ α) (N : ℕ) (f g : ℕ → ℝ) :
    (covariance N f (fun n => g (floorMul α n)) : ℂ) =
      (∑ k ∈ (univ : Finset (ZMod (floorMul α N+1))).erase 0,
        covarianceFourierTerm α N f g k)/((floorMul α N+1 : ℕ) : ℂ) := by
  rw [floor_covariance_fourier hα]
  congr 1
  have hh := sum_erase_add (univ : Finset (ZMod (floorMul α N+1)))
    (covarianceFourierTerm α N f g) (mem_univ 0)
  simpa only [covarianceFourierTerm_zero, add_zero] using hh.symm

noncomputable def frequencyCovariance (α : ℝ) (N : ℕ) (f g : ℕ → ℝ)
    (K : Finset (ZMod (floorMul α N+1))) : ℝ :=
  ((∑ k ∈ K, covarianceFourierTerm α N f g k)/((floorMul α N+1 : ℕ) : ℂ)).re

/-- An exact split into ANY frequency set and its complement. In particular,
smallness on the chosen set does not silently give smallness of its complement. -/
theorem floor_covariance_frequency_split {α : ℝ} (hα : 1 ≤ α) (N : ℕ) (f g : ℕ → ℝ)
    (K : Finset (ZMod (floorMul α N+1))) :
    covariance N f (fun n => g (floorMul α n)) =
      frequencyCovariance α N f g K + frequencyCovariance α N f g Kᶜ := by
  have he : (∑ k ∈ K, covarianceFourierTerm α N f g k)+
      (∑ k ∈ Kᶜ, covarianceFourierTerm α N f g k) =
      ∑ k : ZMod (floorMul α N+1), covarianceFourierTerm α N f g k := by
    exact sum_add_sum_compl K _
  have hh := congrArg Complex.re (floor_covariance_fourier hα N f g)
  simp only [Complex.ofReal_re] at hh
  rw [hh, ← he, add_div, Complex.add_re]
  rfl

/-- Specialization to the actual recentered Vaughan remainders. -/
theorem recentered_fourFactor_frequency_split {α : ℝ} (hα : 1 ≤ α)
    (N U V S T : ℕ) (K : Finset (ZMod (floorMul α N+1))) :
    meanCenteredFourFactor α N U V S T =
      frequencyCovariance α N (fun n => meanCenteredTypeII U V n)
        (fun n => meanCenteredTypeII S T n) K +
      frequencyCovariance α N (fun n => meanCenteredTypeII U V n)
        (fun n => meanCenteredTypeII S T n) Kᶜ :=
  floor_covariance_frequency_split hα N _ _ K

#print axioms floor_covariance_fourier
#print axioms floor_covariance_fourier_nonzero
#print axioms recentered_fourFactor_frequency_split

end Erdos972FloorCovarianceFourier
