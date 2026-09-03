import Submission.ConductorCompletionWeights

/-!
# Vaughan bounds for the grouped smooth-product conductors

This file combines the exact conductor completion bounds with the existing
primitive-character mean estimate. The resulting remainder is explicit; no
smallness at near-full modulus levels is claimed.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

noncomputable def primeProductPositiveModuli (s m : ℕ) : Finset ℕ+ :=
  (primeProductModuli s m).attach.image
    (fun d => ⟨d.val, (primeProductModuli_properties d.property).1⟩)

lemma mem_primeProductPositiveModuli {s m : ℕ} {q : ℕ+} :
    q ∈ primeProductPositiveModuli s m ↔ (q : ℕ) ∈ primeProductModuli s m := by
  constructor
  · intro hq
    obtain ⟨d, hd, heq⟩ := mem_image.mp hq
    have hval := congrArg (fun x : ℕ+ => (x : ℕ)) heq
    change d.val = (q : ℕ) at hval
    exact hval ▸ d.property
  · intro hq
    exact mem_image.mpr ⟨⟨q, hq⟩, mem_attach _ _, Subtype.ext rfl⟩

lemma sum_primeProductPositiveModuli_eq_nat (s m : ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ primeProductPositiveModuli s m, F q) =
      ∑ d ∈ primeProductModuli s m, F d := by
  apply sum_bij (fun (q : ℕ+) _ => (q : ℕ))
  · intro q hq
    exact mem_primeProductPositiveModuli.mp hq
  · intro q hq v hv h
    exact PNat.coe_injective h
  · intro d hd
    let q : ℕ+ := ⟨d, (primeProductModuli_properties hd).1⟩
    exact ⟨q, mem_primeProductPositiveModuli.mpr hd, rfl⟩
  · intro q hq
    rfl

noncomputable def productVaughanMajorant (U V N s m : ℕ) : ℝ :=
  let Q := (progressionScaleN (m + 1)) ^ s
  ((Q : ℝ) ^ 2 * vaughanShortMajorant U V N Q +
    (6 + 2 * Real.log ((N : ℝ) + 1)) *
      ∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j)) /
    (progressionScaleN m : ℝ) ^ s

lemma productVaughanMajorant_nonneg (U V N s m : ℕ) :
    0 ≤ productVaughanMajorant U V N s m := by
  unfold productVaughanMajorant
  apply div_nonneg _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply add_nonneg
  · exact mul_nonneg (sq_nonneg _) (vaughanShortMajorant_nonneg _ _ _ _)
  · apply mul_nonneg
    · have hlog := Real.log_nonneg (show 1 ≤ (N : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) N])
      linarith
    · exact sum_nonneg (fun j _ => Real.sqrt_nonneg _)

/-- The primitive mean at each factor-count group is bounded without
assuming any prime-distribution hypothesis. -/
theorem primitiveProductMangoldtMean_le_vaughan (U V N s m : ℕ)
    (hs : 1 ≤ s) (hV : 1 ≤ V) :
    primitiveProductMangoldtMean s m N ≤ productVaughanMajorant U V N s m := by
  let D := primeProductModuli s m
  let M := primeProductPositiveModuli s m
  let Q := (progressionScaleN (m + 1)) ^ s
  let L : ℝ := (progressionScaleN m : ℝ) ^ s
  let S : ℕ → ℝ := fun d => ∑ ψ ∈ primitiveCharacters d,
    ‖twistedArithmeticSum ψ vonMangoldt N‖
  have hL : 0 < L := by dsimp [L, progressionScaleN]; positivity
  have hQ : 0 < Q := by dsimp [Q, progressionScaleN]; positivity
  have hM : ∀ q ∈ M, 2 ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q := by
    intro q hq
    have hqD := mem_primeProductPositiveModuli.mp hq
    have hp := primeProductModuli_properties hqD
    refine ⟨?_, hp.2.2.2.2⟩
    have hcard : 0 < (q : ℕ).primeFactors.card := by rw [hp.2.2.1]; omega
    have hgt := Nat.nonempty_primeFactors.mp (card_pos.mp hcard)
    omega
  have hmean := primitive_vonMangoldt_mean_bound M Q hQ hM
    (fun q => primitiveCharacters (q : ℕ))
    (fun q hq χ hχ => (mem_filter.mp hχ).2) U V N hV
    (fun _ _ => N) (fun _ _ _ _ => le_rfl)
  have heq : (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient *
      ∑ χ ∈ primitiveCharacters (q : ℕ), ‖twistedArithmeticSum χ vonMangoldt N‖) =
      ∑ d ∈ D, (d : ℝ) / d.totient * S d :=
    sum_primeProductPositiveModuli_eq_nat s m (fun d => (d : ℝ) / d.totient * S d)
  rw [heq] at hmean
  have hweighted : L * primitiveProductMangoldtMean s m N ≤
      ∑ d ∈ D, (d : ℝ) / d.totient * S d := by
    unfold primitiveProductMangoldtMean
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hLd : L ≤ (d : ℝ) := by
      dsimp only [L]
      exact_mod_cast (primeProductModuli_properties hd).2.2.2.1
    have hS : 0 ≤ S d := sum_nonneg (fun χ _ => norm_nonneg _)
    change L * (S d / (d.totient : ℝ)) ≤ (d : ℝ) / d.totient * S d
    calc
      _ ≤ (d : ℝ) * (S d / (d.totient : ℝ)) :=
        mul_le_mul_of_nonneg_right hLd (div_nonneg hS (Nat.cast_nonneg _))
      _ = _ := by ring
  change primitiveProductMangoldtMean s m N ≤ _ / L
  apply (le_div_iff₀ hL).mpr
  rw [mul_comm]
  exact hweighted.trans hmean

lemma primeProductModuli_le_two_pow_mul_totient {r m d : ℕ}
    (hd : d ∈ primeProductModuli r m) : d ≤ 2 ^ r * d.totient := by
  obtain ⟨P, hP, rfl⟩ := mem_image.mp hd
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hP
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (mem_geometricBlockPrimes.mp (hsub hp)).1
  rw [totient_prod_primes P hprime]
  calc
    _ ≤ ∏ p ∈ P, (2 * (p - 1)) := prod_le_prod' (fun p hp => by
      have h := (hprime p hp).two_le
      omega)
    _ = _ := by rw [prod_mul_distrib, prod_const, hcard]

lemma primeProductModuli_add_one_le {r m d : ℕ}
    (hd : d ∈ primeProductModuli r m) :
    (d : ℝ) + 1 ≤ (2 : ℝ) ^ (r + 1) * d.totient := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (primeProductModuli_properties hd).1
  have h : (d : ℝ) ≤ (2 : ℝ) ^ r * d.totient := by
    exact_mod_cast primeProductModuli_le_two_pow_mul_totient hd
  rw [pow_succ]
  nlinarith

lemma prime_product_lift_remainder_le (r m N : ℕ) :
    (∑ d ∈ primeProductModuli r m,
      (((d : ℝ) + 1) * characterLiftError d N) / d.totient) ≤
      (2 : ℝ) ^ (r + 1) * ((primeProductModuli r m).card : ℝ) *
        ((Nat.log 2 N : ℝ) * Real.log ((progressionScaleN (m + 1)) ^ r : ℕ)) := by
  let Q := (progressionScaleN (m + 1)) ^ r
  let E : ℝ := (Nat.log 2 N : ℝ) * Real.log Q
  have hE : 0 ≤ E := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  calc
    _ ≤ ∑ _d ∈ primeProductModuli r m, (2 : ℝ) ^ (r + 1) * E := by
      apply sum_le_sum
      intro d hd
      have hφ : (0 : ℝ) < d.totient := by
        exact_mod_cast Nat.totient_pos.mpr (primeProductModuli_properties hd).1
      have hlift : characterLiftError d N ≤ E :=
        mul_le_mul_of_nonneg_left
          (log_nat_mono (primeProductModuli_properties hd).2.2.2.2) (Nat.cast_nonneg _)
      calc
        _ ≤ (((d : ℝ) + 1) * E) / d.totient :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlift (by positivity)) hφ.le
        _ ≤ (2 : ℝ) ^ (r + 1) * E := by
          apply (div_le_iff₀ hφ).mpr
          have h := mul_le_mul_of_nonneg_right (primeProductModuli_add_one_le hd) hE
          nlinarith only [h]
    _ = _ := by rw [sum_const, nsmul_eq_mul]; dsimp only [E, Q]; ring

/-- Fully explicit remainder from the existing Vaughan estimate, grouped
by conductor size and with logarithmic completion factors retained. -/
theorem prime_product_composite_error_le (r m N : ℕ) (hm : 1 ≤ m)
    (U V : ℕ → ℕ) (hV : ∀ s ∈ Icc 1 r, 1 ≤ V s) :
    (∑ d ∈ primeProductModuli r m, compositeProgressionError d N) ≤
      (∑ s ∈ Icc 1 r, (((2 : ℝ) ^ 64 / ((m : ℝ) + 1)) ^ (r - s) / (r - s).factorial) *
        productVaughanMajorant (U s) (V s) N s m) +
      (2 : ℝ) ^ (r + 1) * ((primeProductModuli r m).card : ℝ) *
        ((Nat.log 2 N : ℝ) * Real.log ((progressionScaleN (m + 1)) ^ r : ℕ)) := by
  have hsplit : (∑ d ∈ primeProductModuli r m, compositeProgressionError d N) =
      (∑ d ∈ primeProductModuli r m, primitiveConductorMangoldtMajorant d N / d.totient) +
      (∑ d ∈ primeProductModuli r m, (((d : ℝ) + 1) * characterLiftError d N) / d.totient) := by
    simp only [compositeProgressionError, add_div, sum_add_distrib]
  rw [hsplit]
  apply _root_.add_le_add _ (prime_product_lift_remainder_le r m N)
  apply (prime_product_conductor_majorant_le r m N).trans
  apply sum_le_sum
  intro s hs
  exact mul_le_mul (primeProductReciprocalMass_upper (r - s) m hm)
    (primitiveProductMangoldtMean_le_vaughan (U s) (V s) N s m (mem_Icc.mp hs).1 (hV s hs))
    (primitiveProductMangoldtMean_nonneg s m N) (by positivity)

noncomputable def productConductorVaughanRemainder (r m N : ℕ) (U V : ℕ → ℕ) : ℝ :=
  (∑ s ∈ Icc 1 r, (((2 : ℝ) ^ 64 / ((m : ℝ) + 1)) ^ (r - s) / (r - s).factorial) *
    productVaughanMajorant (U s) (V s) N s m) +
  (2 : ℝ) ^ (r + 1) * ((primeProductModuli r m).card : ℝ) *
    ((Nat.log 2 N : ℝ) * Real.log ((progressionScaleN (m + 1)) ^ r : ℕ))

theorem prime_product_composite_error_le_remainder (r m N : ℕ) (hm : 1 ≤ m)
    (U V : ℕ → ℕ) (hV : ∀ s ∈ Icc 1 r, 1 ≤ V s) :
    (∑ d ∈ primeProductModuli r m, compositeProgressionError d N) ≤
      productConductorVaughanRemainder r m N U V :=
  prime_product_composite_error_le r m N hm U V hV

/-- Unconditional finite lower bound, with the Vaughan remainder explicit.
The remainder need not be smaller than the main term. -/
theorem prime_product_mangoldt_total_lower_vaughan (r m N : ℕ) (hm : 1 ≤ m)
    (U V : ℕ → ℕ) (hV : ∀ s ∈ Icc 1 r, 1 ≤ V s) :
    mangoldtSum N * primeProductReciprocalMass r m -
      productConductorVaughanRemainder r m N U V ≤
        ∑ d ∈ primeProductModuli r m, residueOneMangoldt d N := by
  have h := composite_progression_total_lower (primeProductModuli r m)
    (fun d hd => (primeProductModuli_properties hd).1) N
  have herr := prime_product_composite_error_le_remainder r m N hm U V hV
  change mangoldtSum N * primeProductReciprocalMass r m - _ ≤ _ at h
  linarith only [h, herr]

end Erdos821
