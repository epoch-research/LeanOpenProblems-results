import Submission.SmoothReciprocalMass
import Submission.KernelSupportEnergyBound

/-! A nonradial support-mass barrier for common lower kernels supported on
squarefree products <=R, with all core primes <=R available. The tail penalty
is explicit. These statements concern a restricted sieve construction, not
the truth or falsity of the quadratic Jacobsthal conjecture. -/
set_option maxHeartbeats 2000000

namespace Erdos970.FiniteSelberg
open Finset Real

/-- Keeping R-smooth terms through R squared gives a coefficient strictly
larger than 3/2 without invoking the asymptotic Mertens-product constant. -/
theorem eulerMass_initial_lower (R : ℕ) (hR : 2 ≤ R) (hL : 1 ≤ log (R : ℝ)) :
    (3 - 2 * log (2 : ℝ)) * log (R : ℝ) - 8 * (WeightedMertens.boundConstant + 1) ≤
      eulerMass (R + 1).primesBelow := by
  let L : ℝ := log (R : ℝ)
  let C : ℝ := WeightedMertens.boundConstant
  have hLp : 0 < L := by dsimp [L]; linarith
  have hRp : 0 < R := by omega
  have hRR : R ≤ R ^ 2 := Nat.le_self_pow (by omega) R
  have hlog : log ((R ^ 2 : ℕ) : ℝ) = 2 * L := by
    rw [Nat.cast_pow, log_pow]
    rfl
  have ha := WeightedMertens.abs_reciprocalInterval_sub_loglog
    (a := (R : ℝ)) (b := ((R ^ 2 : ℕ) : ℝ))
    (by exact_mod_cast hR) (by exact_mod_cast hRR)
  have hlogs : log (log ((R ^ 2 : ℕ) : ℝ)) - log (log (R : ℝ)) = log (2 : ℝ) := by
    rw [hlog, log_mul (by norm_num) hLp.ne']
    change log 2 + log L - log L = log 2
    ring
  rw [hlogs, Nat.cast_pow] at ha
  have hau : WeightedMertens.reciprocalInterval R (R ^ 2) ≤ log 2 + 2 * (C + 1) / L := by
    have hh := (abs_le.mp ha).2
    change WeightedMertens.reciprocalInterval R (R ^ 2) - log 2 ≤ 2 * (C + 1) / L at hh
    linarith
  have hc : 0 < C := WeightedMertens.boundConstant_pos
  have hmul : (1 + 2 * L) * (2 * (C + 1) / L) ≤ 6 * (C + 1) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hLp).mpr
    change 1 ≤ L at hL
    nlinarith only [mul_nonneg (by linarith only [hc] : 0 ≤ C + 1) (by linarith only [hL] : 0 ≤ L - 1)]
  have hat := mul_le_mul_of_nonneg_left hau (by linarith : 0 ≤ 1 + 2 * L)
  have hat' : (1 + 2 * L) * WeightedMertens.reciprocalInterval R (R ^ 2) ≤
      (1 + 2 * L) * log 2 + 6 * (C + 1) := by nlinarith only [hat, hmul]
  have hr1 := (abs_le.mp (WeightedMertens.abs_primeSum_sub_log R hRp)).2
  have hr2 := (abs_le.mp (WeightedMertens.abs_primeSum_sub_log (R ^ 2) (by positivity))).1
  rw [hlog] at hr2
  have hb : L - 2 * C ≤ WeightedMertens.primeSum (R ^ 2) - WeightedMertens.primeSum R := by
    change WeightedMertens.primeSum R - L ≤ C at hr1
    change -C ≤ WeightedMertens.primeSum (R ^ 2) - 2 * L at hr2
    linarith
  have hh := log_le_harmonic_floor (((R ^ 2 : ℕ) : ℝ)) (by positivity)
  rw [Nat.floor_natCast, hlog] at hh
  have he := eulerMass_lower_from_tail R (R ^ 2) hRR
  rw [hlog, Nat.cast_pow] at he
  change (3 - 2 * log 2) * L - 8 * (C + 1) ≤ _
  have hlog2 : log (2 : ℝ) ≤ 2 := by linarith only [log_two_lt_d9]
  nlinarith only [hat', hb, hh, he, hlog2]

noncomputable def supportMassLogThreshold : ℝ :=
  1 + 20 * (8 * (WeightedMertens.boundConstant + 1) + additiveNormalizerConstant + 1)

lemma supportMassLogThreshold_pos : 0 < supportMassLogThreshold := by
  unfold supportMassLogThreshold
  have := WeightedMertens.boundConstant_pos
  have := additiveNormalizerConstant_pos
  positivity

lemma eulerMass_initial_ge_three_halves (R : ℕ) (hR : 2 ≤ R)
    (hL : supportMassLogThreshold ≤ log (R : ℝ)) :
    (3 / 2 : ℝ) * (log (R : ℝ) + additiveNormalizerConstant) ≤
      eulerMass (R + 1).primesBelow := by
  have hc := WeightedMertens.boundConstant_pos
  have hA := additiveNormalizerConstant_pos
  have hL1 : 1 ≤ log (R : ℝ) := by unfold supportMassLogThreshold at hL; nlinarith
  have he := eulerMass_initial_lower R hR hL1
  have hlog2 : log (2 : ℝ) ≤ 7 / 10 := by linarith only [log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_right hlog2 (by linarith : 0 ≤ log (R : ℝ))
  unfold supportMassLogThreshold at hL
  nlinarith only [he, hm, hL, hA, hc]

/-- The normalized mass of divisor support is at most 2/3 beyond a fixed
absolute cutoff. No radial shape assumption is used. -/
theorem initial_divisor_support_mass_le (R : ℕ) (hR : 2 ≤ R)
    (hL : supportMassLogThreshold ≤ log (R : ℝ)) :
    let P := (R + 1).primesBelow
    (∏ p : P, (1 - 1 / (p.val : ℝ))) *
      ∑ Q ∈ divisorSupport (fun p : P => p.val) R,
        weight (fun p : P => 1 / (p.val : ℝ)) Q ≤ 2 / 3 := by
  let P := (R + 1).primesBelow
  have hp (p : P) : p.val.Prime := (WeightedMertens.mem_primes.mp p.property).1
  have hn := indexed_normalizer_log_additive (fun p : P => p.val) hp Subtype.val_injective R
  simp only [normalizer, ← weight_eq_inverse_variance] at hn
  let δ : ℝ := ∏ p : P, (1 - 1 / (p.val : ℝ))
  have hd : 0 < δ := by
    apply prod_pos
    intro p hp'
    have hpp : (1 : ℝ) < p.val := by exact_mod_cast (hp p).one_lt
    have hq : 1 / (p.val : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpp
    linarith
  have he : eulerMass P * δ = 1 := by
    have hprod : (∏ p : P, (1 - 1 / (p.val : ℝ))) = ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
      prod_coe_sort P (fun p : ℕ => 1 - 1 / (p : ℝ))
    unfold eulerMass
    rw [prod_inv_distrib]
    change (∏ p ∈ P, (1 - 1 / (p : ℝ)))⁻¹ * δ = 1
    rw [← hprod]
    exact inv_mul_cancel₀ hd.ne'
  have hEl := mul_le_mul_of_nonneg_right (eulerMass_initial_ge_three_halves R hR hL) hd.le
  change (3 / 2 : ℝ) * (log (R : ℝ) + additiveNormalizerConstant) * δ ≤ eulerMass P * δ at hEl
  rw [he] at hEl
  have hnn := mul_le_mul_of_nonneg_left hn hd.le
  change δ * _ ≤ 2 / 3
  nlinarith only [hEl, hnn]

/-- Common lower-kernel energy minus a tail of mass at least 2/3 cannot be
positive, for ANY function on the divisor support, radial or otherwise. -/
theorem initial_common_kernel_tail_nonpos (R : ℕ) (hR : 2 ≤ R)
    (hL : supportMassLogThreshold ≤ log (R : ℝ))
    (f : Finset (R + 1).primesBelow → ℝ)
    (hf : ∀ Q, Q ∉ divisorSupport (fun p : (R + 1).primesBelow => p.val) R → f Q = 0)
    (T : ℝ) (hT : (2 / 3 : ℝ) ≤ T) :
    kernelEnergy (fun p : (R + 1).primesBelow => 1 / (p.val : ℝ))
      (fun Q => weight (fun p : (R + 1).primesBelow => 1 / (p.val : ℝ)) Q * f Q) -
      T * (∑ Q : Finset (R + 1).primesBelow,
        weight (fun p : (R + 1).primesBelow => 1 / (p.val : ℝ)) Q * f Q ^ 2) ≤ 0 := by
  apply common_tail_energy_nonpos_of_mass _
    (prime_marginals (fun p : (R + 1).primesBelow => p.val)
      (fun p => (WeightedMertens.mem_primes.mp p.property).1)) _ f hf T
  exact (initial_divisor_support_mass_le R hR hL).trans hT

#print axioms eulerMass_initial_lower
#print axioms initial_divisor_support_mass_le
#print axioms initial_common_kernel_tail_nonpos
end Erdos970.FiniteSelberg
