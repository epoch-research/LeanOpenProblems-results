import Submission.RootMeanEulerTransfer

/-!
# Euler transfer for the explicit ideal coefficient model

For the actual ideal-norm Möbius inverse, its local factor is a finite product
of positive factors `1 - p^(-residueDegree)`, at ramified primes as well. Thus
nonnegative normalized coefficients `r`, with the stated prime-power bounds and
prime match, have a positive Euler correction and inherit the positive ideal
mean. No convergence hypothesis on the local ideal-coefficient series is needed
in this specialization. This remains a generic coefficient transfer theorem,
not a claim about a polynomial or a divisor average without supplying its data.
-/

namespace Erdos975Support

open Filter NumberField Ideal Polynomial
open scoped Topology

/-- Evaluate the explicit local inverse polynomial at `1/p`. The weighted local
series is finite because its coefficients are the polynomial coefficients. -/
theorem localFactor_idealNormMobius_eq_prod (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    EulerTransfer.localFactor (idealNormMobiusCoefficients K) p =
      ∏ P ∈ IdealEuler.primesAbove K p,
        (1 - ((p : ℝ)⁻¹) ^ (Ideal.span {(p : ℤ)}).inertiaDeg P) := by
  classical
  let Q : ℤ[X] := idealNormMobiusLocalPolynomial K p
  calc
    EulerTransfer.localFactor (idealNormMobiusCoefficients K) p =
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          EulerTransfer.reciprocal (idealNormMobiusCoefficients K) (p ^ k) := by
      apply tsum_eq_sum
      intro k hk
      have hkdeg : Q.natDegree < k := by
        have hkr : ¬ k < Q.natDegree + 1 := by simpa only [Finset.mem_range] using hk
        omega
      rw [EulerTransfer.reciprocal_apply,
        idealNormMobiusCoefficients_primePow_eq_localPolynomial_coeff K p hp k]
      change (Q.coeff k : ℝ) / ((p ^ k : ℕ) : ℝ) = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkdeg]
      simp
    _ = Polynomial.eval₂ (Int.castRingHom ℝ) (p : ℝ)⁻¹ Q := by
      rw [Polynomial.eval₂_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      rw [EulerTransfer.reciprocal_apply,
        idealNormMobiusCoefficients_primePow_eq_localPolynomial_coeff K p hp k,
        Nat.cast_pow, div_eq_mul_inv, inv_pow]
      rfl
    _ = ∏ P ∈ IdealEuler.primesAbove K p,
        (1 - ((p : ℝ)⁻¹) ^ (Ideal.span {(p : ℤ)}).inertiaDeg P) := by
      dsimp only [Q, idealNormMobiusLocalPolynomial]
      rw [Polynomial.eval₂_finset_prod]
      apply Finset.prod_congr rfl
      intro P _
      simp

/-- Every residue degree occurring in the inverse polynomial is positive. This
is also proved directly from the norm formula and nontriviality of a prime ideal. -/
theorem inertiaDegree_primesAbove_ne_zero (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ IdealEuler.primesAbove K p) :
    (Ideal.span {(p : ℤ)}).inertiaDeg P ≠ 0 := by
  classical
  have hnorm : absNorm P = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg P := by
    simpa using IdealEuler.absNorm_subset_primesAbove_prod K p hp {P} (by simpa)
  intro hdeg
  have hnorm1 : absNorm P = 1 := by simpa [hdeg] using hnorm
  have hPtop : P = ⊤ := Ideal.absNorm_eq_one_iff.mp hnorm1
  exact (IdealEuler.prime_of_mem_primesAbove K p hP).ne_one
    (by simpa only [Ideal.one_eq_top] using hPtop)

/-- Positivity of the actual inverse Euler factor holds at every rational prime,
without removing ramified primes. -/
theorem localFactor_idealNormMobius_pos (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    0 < EulerTransfer.localFactor (idealNormMobiusCoefficients K) p := by
  rw [localFactor_idealNormMobius_eq_prod K p hp]
  apply Finset.prod_pos
  intro P hP
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  exact sub_pos.mpr (pow_lt_one₀ hq0 hq1 (inertiaDegree_primesAbove_ne_zero K p hp P hP))

/-- A nonnegative normalized local root series has a positive ideal correction
factor. The finite ideal inverse makes this proof independent of convergence of
the local ideal-coefficient series. -/
theorem localFactor_idealEulerCorrection_pos (K : Type*) [Field K] [NumberField K]
    (r : ArithmeticFunction ℝ) (hr1 : r 1 = 1) (p : ℕ) (hp : p.Prime)
    (hrnonneg : ∀ k : ℕ, 0 ≤ r (p ^ k)) (C : ℝ)
    (hrbound : ∀ k : ℕ, r (p ^ k) ≤ C) :
    0 < EulerTransfer.localFactor (idealEulerCorrection K r) p := by
  have hvsum : Summable (fun k : ℕ ↦
      EulerTransfer.reciprocal (idealNormMobiusCoefficients K) (p ^ k)) :=
    (EulerTransfer.summable_reciprocal_primePower_of_bound _ p hp
      ((2 : ℝ) ^ Module.finrank ℚ K)
      (abs_idealNormMobiusCoefficients_primePow_le K p hp)).of_norm
  have hrbound' (k : ℕ) : |r (p ^ k)| ≤ C := by
    simpa only [abs_of_nonneg (hrnonneg k)] using hrbound k
  have hrsum := (EulerTransfer.summable_reciprocal_primePower_of_bound r p hp C hrbound').of_norm
  rw [idealEulerCorrection, EulerTransfer.localFactor_mul _ _ p hp hvsum hrsum]
  exact mul_pos (localFactor_idealNormMobius_pos K p hp)
    (EulerTransfer.localFactor_pos_of_nonneg r hr1 p hrnonneg hrsum)

/-- An actual ideal prime model transfers with an absolutely summable and
strictly positive correction. `C` is any common bound at the good primes,
including exponent zero. All exceptional primes have individual finite bounds.
No local or global summability hypothesis on the correction or on the ideal
coefficients occurs in this theorem. -/
theorem summable_abs_idealEulerCorrection_div_and_pos
    (K : Type*) [Field K] [NumberField K] (r : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (hrnonneg : ∀ n : ℕ, 0 ≤ r n)
    (S : Finset ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, r (p ^ k) ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, r (p ^ k) ≤ C)
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = idealNormCoefficients K p) :
    Summable (fun n : ℕ ↦ |idealEulerCorrection K r n| / (n : ℝ)) ∧
      0 < ∑' n : ℕ, idealEulerCorrection K r n / (n : ℝ) := by
  have hbound (p : ℕ) (hp : p.Prime) (B : ℝ)
      (hB : ∀ k : ℕ, r (p ^ k) ≤ B) (k : ℕ) :
      |idealEulerCorrection K r (p ^ k)| ≤ (2 : ℝ) ^ Module.finrank ℚ K * B := by
    apply norm_idealEulerCorrection_primePow_le K r p hp B
      (fun j ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hrnonneg _)] using hB j) k
  have hb : Summable (fun n : ℕ ↦ |idealEulerCorrection K r n| / (n : ℝ)) := by
    apply summable_abs_div_of_primePower_bounds _ (isMultiplicative_idealEulerCorrection K r hr)
      S ((2 : ℝ) ^ Module.finrank ℚ K * C) (by positivity)
    · intro p hp hpS k
      exact hbound p hp C (hrgood p hp hpS) k
    · intro p hp hpS
      exact idealEulerCorrection_prime_eq_zero_of_agree K r hr.1 p hp (hmatch p hp hpS)
    · intro p hp _
      obtain ⟨Cₚ, hCₚ⟩ := hrbounded p hp
      exact ⟨(2 : ℝ) ^ Module.finrank ℚ K * Cₚ, hbound p hp Cₚ hCₚ⟩
  have hnorm : Summable (fun n : ℕ ↦ ‖EulerTransfer.reciprocal (idealEulerCorrection K r) n‖) :=
    hb.congr fun n ↦ by
      rw [EulerTransfer.reciprocal_apply, norm_div, Real.norm_natCast, Real.norm_eq_abs]
  have hpos := EulerTransfer.tsum_pos_of_positive_primePower_series
    (EulerTransfer.reciprocal (idealEulerCorrection K r))
    (EulerTransfer.isMultiplicative_reciprocal _ (isMultiplicative_idealEulerCorrection K r hr))
    hnorm (by
      intro p hp
      obtain ⟨Cₚ, hCₚ⟩ := hrbounded p hp
      exact localFactor_idealEulerCorrection_pos K r hr.1 p hp (fun k ↦ hrnonneg _) Cₚ hCₚ)
  exact ⟨hb, hpos⟩

/-- A positive-exponent degree bound suffices for the preceding theorem. The
extra one in the common bound includes the exponent-zero normalization. -/
theorem summable_abs_idealEulerCorrection_div_and_pos_of_degree
    (K : Type*) [Field K] [NumberField K] (r : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (hrnonneg : ∀ n : ℕ, 0 ≤ r n)
    (S : Finset ℕ) (d : ℕ)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, r (p ^ k) ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, 1 ≤ k → r (p ^ k) ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = idealNormCoefficients K p) :
    Summable (fun n : ℕ ↦ |idealEulerCorrection K r n| / (n : ℝ)) ∧
      0 < ∑' n : ℕ, idealEulerCorrection K r n / (n : ℝ) := by
  apply summable_abs_idealEulerCorrection_div_and_pos K r hr hrnonneg S
    (d + 1 : ℝ) (by positivity) hrbounded _ hmatch
  intro p hp hpS k
  have h := EulerTransfer.abs_primePower_le_degree_add_one r hr.1 d p
    (fun j hj ↦ by simpa only [abs_of_nonneg (hrnonneg _)] using hrgood p hp hpS j hj) k
  simpa only [abs_of_nonneg (hrnonneg _)] using h

/-- The explicit positive mean inherited from the number-field ideal count.
All Euler summability and positivity requirements are discharged in this module;
the input consists only of nonnegative multiplicative coefficients, prime-power
bounds, and a prime match outside a finite set. -/
theorem tendsto_summatory_of_idealEulerCorrection
    (K : Type*) [Field K] [NumberField K] (r : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (hrnonneg : ∀ n : ℕ, 0 ≤ r n)
    (S : Finset ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, r (p ^ k) ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, r (p ^ k) ≤ C)
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = idealNormCoefficients K p) :
    0 < dedekindZeta_residue K * (∑' n : ℕ, idealEulerCorrection K r n / (n : ℝ)) ∧
      Tendsto (fun N : ℕ ↦ arithmeticSummatory r N / (N : ℝ)) atTop
        (𝓝 (dedekindZeta_residue K * ∑' n : ℕ, idealEulerCorrection K r n / (n : ℝ))) := by
  obtain ⟨hb, hpos⟩ := summable_abs_idealEulerCorrection_div_and_pos K r hr hrnonneg
    S C hC0 hrbounded hrgood hmatch
  have hbNorm : Summable (fun n : ℕ ↦ ‖idealEulerCorrection K r n / (n : ℝ)‖) :=
    hb.congr fun n ↦ by rw [norm_div, Real.norm_natCast, Real.norm_eq_abs]
  have ht := tendsto_idealNormCoefficients_convolution K (idealEulerCorrection K r) hbNorm
  rw [idealNormCoefficients_mul_idealEulerCorrection] at ht
  exact ⟨mul_pos (dedekindZeta_residue_pos K) hpos, ht⟩

/-- The same explicit positive mean using a degree bound only at positive
prime-power exponents. This is the form convenient for root-count degree bounds. -/
theorem tendsto_summatory_of_idealEulerCorrection_of_degree
    (K : Type*) [Field K] [NumberField K] (r : ArithmeticFunction ℝ)
    (hr : r.IsMultiplicative) (hrnonneg : ∀ n : ℕ, 0 ≤ r n)
    (S : Finset ℕ) (d : ℕ)
    (hrbounded : ∀ p : ℕ, p.Prime → ∃ Cₚ : ℝ, ∀ k : ℕ, r (p ^ k) ≤ Cₚ)
    (hrgood : ∀ p : ℕ, p.Prime → p ∉ S → ∀ k : ℕ, 1 ≤ k → r (p ^ k) ≤ (d : ℝ))
    (hmatch : ∀ p : ℕ, p.Prime → p ∉ S → r p = idealNormCoefficients K p) :
    0 < dedekindZeta_residue K * (∑' n : ℕ, idealEulerCorrection K r n / (n : ℝ)) ∧
      Tendsto (fun N : ℕ ↦ arithmeticSummatory r N / (N : ℝ)) atTop
        (𝓝 (dedekindZeta_residue K * ∑' n : ℕ, idealEulerCorrection K r n / (n : ℝ))) := by
  apply tendsto_summatory_of_idealEulerCorrection K r hr hrnonneg S
    (d + 1 : ℝ) (by positivity) hrbounded _ hmatch
  intro p hp hpS k
  have h := EulerTransfer.abs_primePower_le_degree_add_one r hr.1 d p
    (fun j hj ↦ by simpa only [abs_of_nonneg (hrnonneg _)] using hrgood p hp hpS j hj) k
  simpa only [abs_of_nonneg (hrnonneg _)] using h

end Erdos975Support
