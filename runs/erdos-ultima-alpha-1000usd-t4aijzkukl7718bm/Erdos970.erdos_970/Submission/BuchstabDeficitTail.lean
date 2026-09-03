import Submission.BuchstabInitialTail

/-! The lower-child deficit in arithmetic prime coordinates, with an exact
fixed-wheel vanishing lemma and a thirteenth-cutoff moment majorant. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

noncomputable def primeIndex (p : ℕ) : ℕ := Nat.count Nat.Prime p
lemma nthPrime_primeIndex (p : ℕ) (hp : p.Prime) : nthPrime (primeIndex p) = p := Nat.nth_count hp
lemma primeIndex_nthPrime (k : ℕ) : primeIndex (nthPrime k) = k :=
  nthPrime_strictMono.injective (nthPrime_primeIndex (nthPrime k) (nthPrime_prime k))

lemma density_primeIndex (p : ℕ) (hp : p.Prime) :
    prefixDensity primeMarginal (primeIndex p) = 1/eulerMass p.primesBelow := by
  rw [nthPrime_prefix_density, nthPrime_primeIndex p hp]

noncomputable def primeLowerDeficit (L : ℝ) (p : ℕ) : ℝ :=
  (1/(p : ℝ))*(1/eulerMass p.primesBelow-referenceLower 0 (primeIndex p) (exp L/(p : ℝ)))

lemma primeLowerDeficit_eq_indexed (k : ℕ) (L : ℝ) :
    primeLowerDeficit L (nthPrime k) = primeMarginal k*(prefixDensity primeMarginal k-
      referenceLower 0 k (exp L*primeMarginal k)) := by
  simp only [primeLowerDeficit, primeIndex_nthPrime, primeMarginal, nthPrime_prefix_density, mul_one_div]

lemma referenceLower_zero_eq_density_on_wheel (k W : ℕ) (hkW : nthPrime k ≤ W)
    (D : ℝ) (hD1 : (W : ℝ)^2 ≤ D) (hD2 : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ D) :
    referenceLower 0 k D = prefixDensity primeMarginal k := by
  have hWpos : 0 < W := (nthPrime_prime k).pos.trans_le hkW
  have hW : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hD : 0 < D := (sq_pos_of_pos hW).trans_le hD1
  have hkeep : primeKeep nthPrime k D := by
    change (nthPrime k : ℝ)^2 ≤ D
    have hkWR : (nthPrime k : ℝ) ≤ W := by exact_mod_cast hkW
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hkWR 2).trans hD1
  have hzero : (∑ p ∈ (nthPrime k).primesBelow, scaledPrimeExcess (log D) p) = 0 := by
    apply sum_eq_zero
    intro p hp
    obtain ⟨hpR,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact scaledPrimeExcess_zero_on_wheel W p hpp (hpR.le.trans hkW) (log D)
      (by simpa only [exp_log hD] using hD2)
  have he := reference_zero_excess_sum k (log D)
  rw [exp_log hD,hzero] at he
  rw [referenceLower, lowerStep_density_identity, if_pos hkeep, he, sub_zero,
    max_eq_right (nthPrime_prefix_density_pos k).le]

lemma primeLowerDeficit_zero_on_wheel (W p : ℕ) (hp : p.Prime) (hpW : p ≤ W)
    (L : ℝ) (hL1 : (W : ℝ)^3 ≤ exp L)
    (hL2 : (W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ exp L) : primeLowerDeficit L p = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpWR : (p : ℝ) ≤ W := by exact_mod_cast hpW
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hD1 : (W : ℝ)^2 ≤ exp L/(p : ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    nlinarith [sq_nonneg (W : ℝ)]
  have hD2 : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp L/(p : ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    have hh := mul_le_mul_of_nonneg_right hpWR
      (mul_nonneg hW0 (sq_nonneg (firstHitWheel W : ℝ)))
    nlinarith only [hL2,hh]
  have he := referenceLower_zero_eq_density_on_wheel (primeIndex p) W
    (by simpa only [nthPrime_primeIndex p hp] using hpW) (exp L/(p : ℝ)) hD1 hD2
  rw [density_primeIndex p hp] at he
  simp only [primeLowerDeficit, he, sub_self, mul_zero]

lemma primeLowerDeficit_le_thirteenth (p : ℕ) (hp : p.Prime) (L : ℝ) (hL : 0 < L)
    (hpL : 13*log (p : ℝ) ≤ L)
    (hthreshold : supportMassLogThreshold ≤ log (p : ℝ))
    (hprofile : ∀ v : ℝ, 9 ≤ v → (1/eulerMass p.primesBelow)*(1-(4/525 : ℝ)*(9/v)^8) ≤
      referenceLower 0 (primeIndex p) (exp (v*log (p : ℝ)))) :
    primeLowerDeficit L p ≤ (lowerTailCoefficient/L^8)*(log (p : ℝ)^7/p) := by
  let v := L/log (p : ℝ)-1
  let E := eulerMass p.primesBelow
  have hlogp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hvprod : (v+1)*log (p : ℝ) = L := by dsimp [v]; field_simp; ring
  have hv : 12 ≤ v := by nlinarith only [hvprod,hpL,hlogp]
  have he : exp (v*log (p : ℝ)) = exp L/(p : ℝ) := by
    rw [show v*log (p : ℝ) = L-log (p : ℝ) by nlinarith only [hvprod], exp_sub, exp_log hpR]
  have hf := hprofile v (by linarith)
  rw [he] at hf
  have hdef : 1/E-referenceLower 0 (primeIndex p) (exp L/(p : ℝ)) ≤
      (1/E)*(4/525 : ℝ)*(9/v)^8 := by nlinarith only [hf]
  have hE : 0 < E := eulerMass_pos _ (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hEinv : 1/E ≤ 1/((3/2 : ℝ)*log (p : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (eulerMass_strict_prefix_ge_three_halves p hp hthreshold)
  have hr : 9/v ≤ (39/4 : ℝ)*log (p : ℝ)/L := by
    apply (div_le_div_iff₀ (by linarith : 0 < v) hL).mpr
    nlinarith only [hvprod,hpL]
  have hp8 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 9/v) hr 8
  have htail : (1/E)*(4/525 : ℝ)*(9/v)^8 ≤
      (1/((3/2 : ℝ)*log (p : ℝ)))*(4/525 : ℝ)*((39/4 : ℝ)*log (p : ℝ)/L)^8 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hEinv (by norm_num)) hp8
      (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left (hdef.trans htail) (one_div_pos.mpr hpR).le
  convert hh using 1
  dsimp only [lowerTailCoefficient]
  field_simp
  <;> ring

#print axioms referenceLower_zero_eq_density_on_wheel
#print axioms primeLowerDeficit_zero_on_wheel
#print axioms primeLowerDeficit_le_thirteenth
end Erdos970.RecursiveSieve.Buchstab
