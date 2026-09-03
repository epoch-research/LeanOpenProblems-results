import Submission.SelbergQuadraticProfile

/-! Positive energy for the quadratic logarithmic profile with reciprocal tail
at most5/24. This is not yet an interval or Jacobsthal bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def quadraticEnergyOffset : ℝ := normalizerOffset 65537 + 1
noncomputable def quadraticEnergyError : ℝ :=
  1 + 21 * WeightedMertens.sharpMomentError + 8 * quadraticEnergyOffset +
    16 * quadraticEnergyOffset * WeightedMertens.sharpMomentError

lemma quadraticEnergyOffset_pos : 0 < quadraticEnergyOffset := by
  have := normalizerOffset_pos 65537
  unfold quadraticEnergyOffset
  positivity

lemma quadraticEnergyError_pos : 0 < quadraticEnergyError := by
  have := quadraticEnergyOffset_pos
  have := WeightedMertens.sharpMomentError_pos
  unfold quadraticEnergyError
  positivity

/-- The leading square mass8/15 dominates the Dirichlet contribution94/225
and the stated tail, with all lower-order and accuracy errors retained. -/
theorem prime_quadratic_energy_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hL : 1 ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 5 / 24) :
    log (R : ℝ) ^ 5 / 256 - quadraticEnergyError * log (R : ℝ) ^ 4 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeQuadraticProfile p (log R) Q) := by
  let L := log (R : ℝ)
  let U := cappedLogMoment p L 2
  let V := cappedLogMoment p L 3
  let W := cappedLogMoment p L 5
  let T := ∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)
  let C := quadraticEnergyOffset
  let e := WeightedMertens.sharpMomentError
  let E := L / 65536 + C
  have hL0 : 0 ≤ L := log_natCast_nonneg R
  have hC : 0 < C := quadraticEnergyOffset_pos
  have he : 0 < e := WeightedMertens.sharpMomentError_pos
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hm2 := WeightedMertens.prime_log_moment R hR 0
  have hm3 := WeightedMertens.prime_log_moment R hR 1
  have hm5 := WeightedMertens.prime_fifth_log_moment R hR
  norm_num only [Nat.reduceAdd, Nat.cast_zero, Nat.cast_one, zero_add, one_add_one_eq_two,
    show (1 : ℝ) + 2 = 3 by norm_num, pow_one] at hm2 hm3
  have hU : U ≤ L ^ 2 / 2 + 2 * e * L + L ^ 2 * T := by
    dsimp [U]
    rw [cappedLogMoment_split p hp hinj R hR hfull 2]
    have hh := (abs_le.mp hm2).2
    dsimp [L, e, T]
    linarith
  have hV : L ^ 3 / 3 - 2 * e * L ^ 2 + L ^ 3 * T ≤ V := by
    dsimp [V]
    rw [cappedLogMoment_split p hp hinj R hR hfull 3]
    have hh := (abs_le.mp hm3).1
    dsimp [L, e, T]
    linarith
  have hW : L ^ 5 / 5 - 2 * e * L ^ 4 + L ^ 5 * T ≤ W := by
    dsimp [W]
    rw [cappedLogMoment_split p hp hinj R hR hfull 5]
    have hh := (abs_le.mp hm5).1
    dsimp [L, e, T]
    linarith
  have hu := mul_le_mul_of_nonneg_left hU
    (show 0 ≤ (4 / 3 : ℝ) * L ^ 3 by positivity)
  have hv := mul_le_mul_of_nonneg_left hV
    (show 0 ≤ (2 / 3 : ℝ) * L ^ 2 by positivity)
  have hw := mul_le_mul_of_nonneg_left hW (show 0 ≤ (2 / 15 : ℝ) by norm_num)
  have ht := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ (8 / 15 : ℝ) * L ^ 5 by positivity)
  change (8 / 15 : ℝ) * L ^ 5 * T ≤ _ at ht
  have hcore : (4 / 3) * L ^ 3 * U - (2 / 3) * L ^ 2 * V - (2 / 15) * W ≤
      (119 / 225) * L ^ 5 + (64 / 15) * e * L ^ 4 := by
    nlinarith only [hu, hv, hw, ht]
  have ht2 := mul_le_mul_of_nonneg_left htail (sq_nonneg L)
  change L ^ 2 * T ≤ _ at ht2
  have hrough : U ≤ L ^ 2 + 2 * e * L := by nlinarith only [hU, ht2, sq_nonneg L]
  have hrough' := mul_le_mul_of_nonneg_left hrough
    (show 0 ≤ 8 * E * L ^ 2 by positivity)
  have hL34 : L ^ 3 ≤ L ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right hL (pow_nonneg hL0 3)
    change 1 * L ^ 3 ≤ L * L ^ 3 at hh
    nlinarith only [hh]
  have hCE := mul_le_mul_of_nonneg_left hL34 (show 0 ≤ 16 * C * e by positivity)
  have he4 : 0 ≤ e * L ^ 4 := by positivity
  have hvar : 8 * E * L ^ 2 * U ≤
      L ^ 5 / 8192 + (8 * C + 16 * e + 16 * C * e) * L ^ 4 := by
    dsimp only [E] at hrough' ⊢
    nlinarith only [hrough', hCE, he4]
  have hnorm := prime_quadratic_square_lower p hp hinj R hR hfull
  have hdir := prime_quadratic_dirichlet_le p hp hinj R hR hfull 65536 (by norm_num)
  change (∑ i, (1 / (p i : ℝ)) * ∑ Q ∈ (univ.erase i).powerset,
    weight (fun i => 1 / (p i : ℝ)) Q *
      (primeQuadraticProfile p L Q - primeQuadraticProfile p L (insert i Q)) ^ 2) ≤
    (4 / 3) * L ^ 3 * U - (2 / 3) * L ^ 2 * V - (2 / 15) * W +
      8 * (L / 65536 + normalizerOffset 65537 + 1) * L ^ 2 * U at hdir
  have hEE : L / 65536 + normalizerOffset 65537 + 1 = E := by dsimp [E, C, quadraticEnergyOffset]; ring
  rw [hEE] at hdir
  rw [kernelEnergy_weighted _ (prime_marginals p hp)]
  change L ^ 5 / 256 - quadraticEnergyError * L ^ 4 ≤ _
  change (8 / 15) * L ^ 5 - L ^ 4 ≤ _ at hnorm
  have hD : quadraticEnergyError = 1 + 21 * e + 8 * C + 16 * C * e := rfl
  rw [hD]
  have hL5 : 0 ≤ L ^ 5 := by positivity
  nlinarith only [hnorm, hdir, hcore, hvar, hL5, he4]

/-- Once the fixed lower-order error is absorbed, the energy has a fixed
positive multiple of L^5. The reciprocal-tail hypothesis remains explicit. -/
theorem prime_quadratic_energy (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hL : 1 ≤ log (R : ℝ)) (hlarge : 512 * quadraticEnergyError ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 5 / 24) :
    log (R : ℝ) ^ 5 / 512 ≤
      kernelEnergy (fun i => 1 / (p i : ℝ))
        (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeQuadraticProfile p (log R) Q) := by
  have hh := prime_quadratic_energy_lower p hp hinj R hR hfull hL htail
  have hm := mul_le_mul_of_nonneg_right hlarge (pow_nonneg (log_natCast_nonneg R) 4)
  nlinarith only [hh, hm]

#print axioms prime_quadratic_energy_lower
#print axioms prime_quadratic_energy
end Erdos970.FiniteSelberg
