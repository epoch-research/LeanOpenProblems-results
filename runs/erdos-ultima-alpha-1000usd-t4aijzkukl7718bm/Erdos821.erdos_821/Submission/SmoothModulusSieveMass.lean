import Submission.SmoothModulusSpacing

/-!
# A cardinality lower bound for smooth-modulus large-sieve constants

The number of reduced residue fractions at the smooth product moduli is
quadratic in the modulus scale, up to polynomial factors in the scale index.
A single constant Fourier mode therefore forces the same scale in every
additive large-sieve estimate that is uniform over coefficients.

This is stronger than a minimum-spacing obstruction, but does not rule out
estimates specialized to arithmetic coefficients or signed averages. It does
not prove or disprove Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

lemma primeProductModuli_totient_lower {r m d : ℕ}
    (hd : d ∈ primeProductModuli r m) :
    (progressionScaleN m) ^ r ≤ d.totient := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hSP, hcard⟩ := Finset.mem_powersetCard.mp hS
  have hprime : ∀ p ∈ S, p.Prime := fun p hp =>
    (mem_geometricBlockPrimes.mp (hSP hp)).1
  rw [totient_prod_primes S hprime]
  calc
    _ = ∏ _p ∈ S, progressionScaleN m := by simp only [Finset.prod_const, hcard]
    _ ≤ _ := Finset.prod_le_prod' (fun p hp => by
      have h := (mem_geometricBlockPrimes.mp (hSP hp)).2.1
      omega)

lemma prime_product_totient_mass_lower (r m : ℕ)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m) :
    2 ^ (128 * r * m) ≤ 4096 ^ r * r.factorial * (m + 1) ^ r *
      ∑ d ∈ primeProductModuli r m, d.totient := by
  have hcount := primeProductModuli_polynomial_count r m hsmall
  have hmass : (primeProductModuli r m).card * (progressionScaleN m) ^ r ≤
      ∑ d ∈ primeProductModuli r m, d.totient := by
    calc
      _ = ∑ _d ∈ primeProductModuli r m, (progressionScaleN m) ^ r := by simp
      _ ≤ _ := Finset.sum_le_sum (fun d hd => primeProductModuli_totient_lower hd)
  calc
    _ = (progressionScaleN m) ^ r * (progressionScaleN m) ^ r := by
      simp only [progressionScaleN, ← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ (4096 ^ r * r.factorial * (m + 1) ^ r * (primeProductModuli r m).card) *
        (progressionScaleN m) ^ r := Nat.mul_le_mul_right _ hcount
    _ = (4096 ^ r * r.factorial * (m + 1) ^ r) *
        ((primeProductModuli r m).card * (progressionScaleN m) ^ r) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmass

/-- The sum of squared samples at all reduced residue fractions. It uses
natural residues so that the zero-modulus edge case is harmless. -/
noncomputable def reducedResidueEnergy (D : Finset ℕ) (A : Finset ℤ) (a : ℤ → ℂ) : ℝ :=
  ∑ d ∈ D, ∑ u ∈ (Finset.range d).filter (fun u => d.Coprime u),
    ‖trigSum A a ((u : ℝ) / d)‖ ^ 2

lemma reduced_residue_energy_constant_mode (D : Finset ℕ) (A : Finset ℤ)
    (hA : 0 ∈ A) :
    reducedResidueEnergy D A (fun n => if n = 0 then 1 else 0) =
      ∑ d ∈ D, (d.totient : ℝ) := by
  have hsum (x : ℝ) : trigSum A (fun n => if n = 0 then 1 else 0) x = 1 := by
    simp [trigSum, wave, hA]
  simp only [reducedResidueEnergy, hsum, norm_one, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one, ← Nat.totient_eq_card_coprime]

/-- Any uniform coefficient bound on a frequency set containing zero must
pay at least the total number of reduced residues. This does not use a
minimum-spacing estimate. -/
lemma uniform_reduced_residue_constant_lower (D : Finset ℕ) (A : Finset ℤ)
    (hA : 0 ∈ A) (B : ℝ)
    (H : ∀ a : ℤ → ℂ, reducedResidueEnergy D A a ≤ B * ∑ n ∈ A, ‖a n‖ ^ 2) :
    (∑ d ∈ D, (d.totient : ℝ)) ≤ B := by
  have h := H (fun n => if n = 0 then 1 else 0)
  rw [reduced_residue_energy_constant_mode D A hA] at h
  have he : (∑ n ∈ A, ‖(if n = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1 := by
    calc
      _ = ∑ n ∈ A, if n = 0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        split_ifs <;> norm_num
      _ = 1 := by simp [hA]
  simpa only [he, mul_one] using h

theorem prime_product_uniform_additive_constant_lower (r m : ℕ)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m)
    (A : Finset ℤ) (hA : 0 ∈ A) (B : ℝ)
    (H : ∀ a : ℤ → ℂ, reducedResidueEnergy (primeProductModuli r m) A a ≤
      B * ∑ n ∈ A, ‖a n‖ ^ 2) :
    (2 : ℝ) ^ (128 * r * m) ≤
      (4096 : ℝ) ^ r * r.factorial * ((m : ℝ) + 1) ^ r * B := by
  have hlo : (2 : ℝ) ^ (128 * r * m) ≤
      (4096 : ℝ) ^ r * r.factorial * ((m : ℝ) + 1) ^ r *
        ∑ d ∈ primeProductModuli r m, (d.totient : ℝ) := by
    exact_mod_cast prime_product_totient_mass_lower r m hsmall
  exact hlo.trans (mul_le_mul_of_nonneg_left
    (uniform_reduced_residue_constant_lower _ A hA B H) (by positivity))

/-- The reduced-residue mass is larger than every fixed subquadratic power
of the lower modulus scale, in this integer-power formulation. The arbitrary
constant C makes the assertion insensitive to fixed multiplicative factors. -/
theorem eventually_prime_product_totient_mass_power_lower (r k C : ℕ)
    (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∀ᶠ m : ℕ in atTop,
      C * 2 ^ (64 * r * (2 * k - 1) * m) ≤
        (∑ d ∈ primeProductModuli r m, d.totient) ^ k := by
  let c := 4096 ^ r * r.factorial
  filter_upwards [eventually_nat_poly_le_two_pow 1 (4096 * r) 1,
    eventually_nat_poly_le_two_pow 1 (C * c ^ k) (r * k)] with m hm₁ hm₂
  have hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m := by
    have h : 4096 * r * (m + 1) ≤ 2 ^ m := by simpa only [one_mul, pow_one] using hm₁
    exact h.trans (Nat.pow_le_pow_right (by decide) (by omega))
  let K := c * (m + 1) ^ r
  let S := ∑ d ∈ primeProductModuli r m, d.totient
  have hK : 0 < K := by dsimp [K, c]; positivity
  have hbudget : C * K ^ k ≤ 2 ^ (64 * r * m) := by
    have h : C * c ^ k * (m + 1) ^ (r * k) ≤ 2 ^ m := by
      simpa only [one_mul] using hm₂
    calc
      _ = C * c ^ k * (m + 1) ^ (r * k) := by dsimp [K]; rw [mul_pow, pow_mul]; ring
      _ ≤ 2 ^ m := h
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [hr])
  have hmass : 2 ^ (128 * r * m) ≤ K * S := prime_product_totient_mass_lower r m hsmall
  have hpow : 2 ^ ((128 * r * m) * k) ≤ K ^ k * S ^ k := by
    simpa only [pow_mul, mul_pow] using Nat.pow_le_pow_left hmass k
  have hexp : 64 * r * m + 64 * r * (2 * k - 1) * m = 128 * r * m * k := by
    have h := congrArg (fun z : ℕ => 64 * r * m * z)
      (Nat.sub_add_cancel (show 1 ≤ 2 * k by omega))
    nlinarith only [h]
  have hle : K ^ k * (C * 2 ^ (64 * r * (2 * k - 1) * m)) ≤ K ^ k * S ^ k := by
    calc
      _ = (C * K ^ k) * 2 ^ (64 * r * (2 * k - 1) * m) := by ring
      _ ≤ 2 ^ (64 * r * m) * 2 ^ (64 * r * (2 * k - 1) * m) :=
        Nat.mul_le_mul_right _ hbudget
      _ = 2 ^ ((128 * r * m) * k) := by rw [← pow_add, hexp]
      _ ≤ _ := hpow
  exact Nat.le_of_mul_le_mul_left hle (pow_pos hK k)

end Erdos821
