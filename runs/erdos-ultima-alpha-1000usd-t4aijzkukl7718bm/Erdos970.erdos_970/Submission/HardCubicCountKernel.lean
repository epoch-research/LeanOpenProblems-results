import Submission.KernelSurvivorCount
import Submission.HardCubicEnergyThreshold

/-! An explicit count version of the hard-cubic lower sieve. Its scale is
still that of the previously verified exponent 5/2, not the quadratic target. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000

lemma additiveNormalizerConstant_le_energyThreshold :
    additiveNormalizerConstant ≤ hardCubicEnergyThreshold := by
  unfold hardCubicEnergyThreshold
  have hA := additiveNormalizerConstant_pos
  have hM := WeightedMertens.sharpMomentError_pos
  have hJ := hardCubicJumpScale_pos
  have hC := WeightedMertens.boundConstant_pos
  have hS : 0 ≤ (hardCubicSmallSplit : ℝ) := Nat.cast_nonneg _
  nlinarith only [hA, hM, hJ, hC, hS,
    mul_nonneg hJ.le (by linarith only [hS] : 0 ≤ (hardCubicSmallSplit : ℝ) + 1)]

lemma prime_hardCubic_mass_bounds (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hL : additiveNormalizerConstant ≤ log (R : ℝ)) :
    0 ≤ (∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) ∧
    (∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) ≤
      20000 * log (R : ℝ) ^ 4 := by
  let q : ι → ℝ := fun i => 1 / (p i : ℝ)
  let f := primeHardCubicProfile p (log R)
  let D := divisorSupport p R
  have hb (Q : Finset ι) : 0 ≤ f Q ∧ f Q ≤ 10000 * log (R : ℝ) ^ 3 :=
    hardCubicProfile_bounds (log R) (primeLogLocation p Q) (log_natCast_nonneg R)
      (primeLogLocation_nonneg p Q)
  have hw (Q : Finset ι) : 0 ≤ weight q Q := (weight_pos q (prime_marginals p hp) Q).le
  refine ⟨sum_nonneg (fun Q _ => mul_nonneg (hw Q) (hb Q).1), ?_⟩
  have hn := indexed_normalizer_log_additive p hp hinj R
  simp only [normalizer, ← weight_eq_inverse_variance] at hn
  have he : (∑ Q : Finset ι, weight q Q * f Q) = ∑ Q ∈ D, weight q Q * f Q := by
    symm
    apply sum_subset (subset_univ D)
    intro Q hQ hQD
    rw [show f Q = 0 from prime_hardCubic_support p hp R hR Q hQD, mul_zero]
  change (∑ Q : Finset ι, weight q Q * f Q) ≤ _
  rw [he]
  calc
    _ ≤ 10000 * log (R : ℝ) ^ 3 * ∑ Q ∈ D, weight q Q := by
      rw [mul_sum]
      apply sum_le_sum
      intro Q hQ
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb Q).2 (hw Q)
    _ ≤ 10000 * log (R : ℝ) ^ 3 * (log R + additiveNormalizerConstant) :=
      mul_le_mul_of_nonneg_left hn (by have := log_natCast_nonneg R; positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hL
        (show 0 ≤ 10000 * log (R : ℝ) ^ 3 by have := log_natCast_nonneg R; positivity)
      nlinarith only [hh]

lemma prime_hardCubic_cost_square (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R) :
    kernelCost (fun i => 1 / (p i : ℝ))
      (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) ^ 2 ≤
      100000000 * exp 4 * (R : ℝ) ^ 2 * log (R : ℝ) ^ 6 := by
  have hc := prime_hardCubic_cost_le p hp hinj R hR
  have hnon : 0 ≤ kernelCost (fun i => 1 / (p i : ℝ))
      (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) :=
    sum_nonneg (fun _ _ => abs_nonneg _)
  have hh := pow_le_pow_left₀ hnon hc 2
  have he : (exp (2 : ℝ)) ^ 2 = exp 4 := by rw [← exp_nat_mul]; norm_num
  calc
    _ ≤ (10000 * log (R : ℝ) ^ 3 * exp 2 * R) ^ 2 := hh
    _ = 100000000 * (exp 2) ^ 2 * (R : ℝ) ^ 2 * log (R : ℝ) ^ 6 := by ring
    _ = _ := by rw [he]

/-- Once twice the absolute error budget is paid, a positive proportion of
m/log R survives. All arithmetic size assumptions are explicit. -/
theorem prime_hardCubic_count (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (hlarge : hardCubicEnergyThreshold ≤ log (R : ℝ))
    (htail : (∑ i ∈ univ.filter (fun i => R < p i), 1 / (p i : ℝ)) ≤ 2877 / 10000)
    (r : ℕ → ℕ) (m : ℕ)
    (hm : 2 * 100000000 * exp 4 * (Fintype.card ι + 1 : ℝ) * (R : ℝ) ^ 2 ≤
      (m : ℝ) * log R) :
    (m : ℝ) ≤ 800000000 * log R *
      (((range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) := by
  let L := log (R : ℝ)
  let q : ι → ℝ := fun i => 1 / (p i : ℝ)
  let c : Finset ι → ℝ := fun Q => weight q Q * primeHardCubicProfile p L Q
  let N : ℝ := (((range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ)
  have hL : 0 < L := hardCubicEnergyThreshold_pos.trans_le hlarge
  have hL6 : 0 ≤ L ^ 6 := pow_nonneg hL.le _
  have hcard : 0 ≤ (Fintype.card ι + 1 : ℝ) := by positivity
  have he : L ^ 7 ≤ kernelEnergy q c := prime_hardCubic_energy p hp hinj R hR hfull hlarge htail
  have hcost : kernelCost q c ^ 2 ≤ 100000000 * exp 4 * (R : ℝ) ^ 2 * L ^ 6 :=
    prime_hardCubic_cost_square p hp hinj R hR
  have hc := mul_le_mul_of_nonneg_left hcost hcard
  have hm' := mul_le_mul_of_nonneg_right hm hL6
  change 2 * 100000000 * exp 4 * (Fintype.card ι + 1 : ℝ) * (R : ℝ) ^ 2 * L ^ 6 ≤
    (m : ℝ) * L * L ^ 6 at hm'
  have herr : 2 * ((Fintype.card ι + 1 : ℝ) * kernelCost q c ^ 2) ≤ (m : ℝ) * L ^ 7 := by
    nlinarith only [hc, hm']
  obtain ⟨hc0, hcm⟩ := prime_hardCubic_mass_bounds p hp hinj R hR
    (additiveNormalizerConstant_le_energyThreshold.trans hlarge)
  change 0 ≤ ∑ Q : Finset ι, c Q at hc0
  change (∑ Q : Finset ι, c Q) ≤ 20000 * L ^ 4 at hcm
  have hcsq : (∑ Q : Finset ι, c Q) ^ 2 ≤ 400000000 * L ^ 8 := by
    have hh := pow_le_pow_left₀ hc0 hcm 2
    nlinarith only [hh]
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hmass := mul_le_mul_of_nonneg_right hcsq hN
  have hmain := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg m)
  have hlo := prime_survivor_count_lower_kernel p hp hinj c r m
  change (m : ℝ) * kernelEnergy q c - (Fintype.card ι + 1 : ℝ) * kernelCost q c ^ 2 ≤
    (∑ Q : Finset ι, c Q) ^ 2 * N at hlo
  have hh : (m : ℝ) * L ^ 7 ≤ (800000000 * L * N) * L ^ 7 := by
    nlinarith only [hmain, hlo, hmass, herr]
  exact (mul_le_mul_iff_left₀ (pow_pos hL 7)).mp hh

#print axioms prime_hardCubic_mass_bounds
#print axioms prime_hardCubic_count
end Erdos970.FiniteSelberg
