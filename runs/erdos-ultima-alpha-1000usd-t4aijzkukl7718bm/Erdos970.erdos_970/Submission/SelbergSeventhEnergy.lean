import Submission.SelbergCubicEnergy

/-! Positive soft energy allowing reciprocal tail up to 1/7. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sharp moment coefficients leave a fixed positive cubic main term. -/
theorem prime_soft_energy_seventh_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hL : 1 ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 1 / 7) :
    log (R : ℝ) ^ 3 / 512 - cubicEnergyError * log (R : ℝ) ^ 2 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q *
          softProfile (fun i => log (p i : ℝ)) (log R) Q) := by
  let L := log (R : ℝ)
  let U := cappedLogMoment p L 2
  let V := cappedLogMoment p L 3
  let T := ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)
  let C := normalizerOffset 65
  let e := WeightedMertens.sharpMomentError
  have hC : 0 < C := normalizerOffset_pos 65
  have he : 0 < e := WeightedMertens.sharpMomentError_pos
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hmoment := WeightedMertens.prime_second_third_log_moments R hR
  have hU : U ≤ L ^ 2 / 2 + 2 * e * L + L ^ 2 * T := by
    dsimp [U]
    rw [cappedLogMoment_split p hp hinj R hR hfull 2]
    have hh := (abs_le.mp hmoment.1).2
    change _ ≤ _ at hh
    dsimp [e, L, T]
    linarith
  have hV : L ^ 3 / 3 - 4 * e * L ^ 2 + L ^ 3 * T ≤ V := by
    dsimp [V]
    rw [cappedLogMoment_split p hp hinj R hR hfull 3]
    have hh := (abs_le.mp hmoment.2).1
    dsimp [e, L, T]
    linarith
  have hnorm := prime_soft_square_lower p hp hinj R hR hfull
  have hdir := prime_soft_dirichlet_le p hp hinj L hL0
  have hbase : L ^ 3 / 3 - L ^ 2 -
      (((65 / 64) * L + C) * U - (2 / 3) * (65 / 64) * V) ≤
        kernelEnergy (fun i => 1 / (p i : ℝ))
          (fun Q => weight (fun i => 1 / (p i : ℝ)) Q *
            softProfile (fun i => log (p i : ℝ)) L Q) := by
    rw [kernelEnergy_weighted _ (prime_marginals p hp)]
    dsimp only [U, V, C] at *
    change L ^ 3 / 3 - L ^ 2 ≤ _ at hnorm
    nlinarith only [hnorm, hdir]
  apply le_trans ?_ hbase
  change L ^ 3 / 512 - cubicEnergyError * L ^ 2 ≤ _
  have hU' := mul_le_mul_of_nonneg_left hU
    (show 0 ≤ (65 / 64 : ℝ) * L + C by positivity)
  have hV' := mul_le_mul_of_nonneg_left hV
    (show 0 ≤ (2 / 3 : ℝ) * (65 / 64) by norm_num)
  have hT' := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ ((65 / 64 : ℝ) / 3) * L ^ 3 + C * L ^ 2 by positivity)
  change (((65 / 64 : ℝ) / 3) * L ^ 3 + C * L ^ 2) * T ≤ _ at hT'
  have hCE := mul_le_mul_of_nonneg_left
    (show L ≤ L ^ 2 by change 1 ≤ L at hL; nlinarith)
    (show 0 ≤ 2 * C * e by positivity)
  have heL : 0 ≤ e * L ^ 2 := by positivity
  have hCL : 0 ≤ C * L ^ 2 := by positivity
  have hL3 : 0 ≤ L ^ 3 := by positivity
  have hD : cubicEnergyError = 1 + 5 * (65 / 64) * e + 2 * C * (1 + e) := rfl
  rw [hD]
  nlinarith only [hU', hV', hT', hCE, heL, hCL, hL3]

/-- A sufficiently large logarithmic cutoff gives energy at least log(R)^3/1024. -/
theorem prime_soft_energy_seventh (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hL : 1 ≤ log (R : ℝ)) (hlarge : 1024 * cubicEnergyError ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 1 / 7) :
    log (R : ℝ) ^ 3 / 1024 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q *
          softProfile (fun i => log (p i : ℝ)) (log R) Q) := by
  have hh := prime_soft_energy_seventh_lower p hp hinj R hR hfull hL htail
  have he := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (log (R : ℝ)))
  nlinarith only [hh, he]


#print axioms prime_soft_energy_seventh
end Erdos970.FiniteSelberg
