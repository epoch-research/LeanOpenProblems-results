import Submission.RoughProgressions
import Submission.PrimitiveProductCharacters

/-!
# A second sieve for smooth composite moduli

The large prime factor of a nonsmooth predecessor is coprime to every smooth
progression modulus. The resulting prime-pair bound retains the reciprocal
totient main term, without a factor exponential in the number of prime factors.
These are upper bounds for the rejected primes, not a settlement of Erdős 821.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821.AnalyticSieve

lemma composite_cofactor_totient_ratio_sq {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    ((2 * ((d * k : ℕ) : ℝ)) / Nat.totient (2 * (d * k))) ^ 2 ≤
      ((d : ℝ) / d.totient) ^ 2 * ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 := by
  have h := totient_ratio_submultiplicative d (2 * k) hd (by omega)
  have heq : d * (2 * k) = 2 * (d * k) := by ring
  rw [heq] at h
  have hratio : (2 * ((d * k : ℕ) : ℝ)) / Nat.totient (2 * (d * k)) ≤
      ((d : ℝ) / d.totient) * ((2 * (k : ℝ)) / Nat.totient (2 * k)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hsq := pow_le_pow_left₀ (by positivity) hratio 2
  simpa only [mul_pow] using hsq

lemma sum_prime_pair_composite_cofactor_bound (X K J d : ℕ) (hd : 0 < d)
    (hKX : d * K ≤ X) (hJ : 0 < J) :
    (∑ k ∈ Finset.Icc 1 K, (primePairCofactorCount X (d * k) : ℝ)) ≤
      (16 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * ((d : ℝ) / (d.totient : ℝ) ^ 2) +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  let D : ℝ := ((J : ℝ) * Real.log 2) ^ 2
  let E : ℝ := (2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hb (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      (primePairCofactorCount X (d * k) : ℝ) ≤
        (4 * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
          (((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + E := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    have hkX : d * k ≤ X := (Nat.mul_le_mul_left d (mem_Icc.mp hk).2).trans hKX
    have hp := prime_pair_cofactor_bound X (d * k) J (Nat.mul_pos hd hk0) hkX hJ
    apply hp.trans
    calc
      _ ≤ (4 * (X : ℝ) / D) *
          ((((d : ℝ) / d.totient)^2 * ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2) /
            ((d * k : ℕ) : ℝ)) + E := by
        gcongr
        exact composite_cofactor_totient_ratio_sq hd hk0
      _ = _ := by
        push_cast
        field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((4 * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
        (((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + E) := sum_le_sum hb
    _ = (4 * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
        (∑ k ∈ Finset.Icc 1 K, ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + (K : ℝ) * E := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ (4 * (X : ℝ) * d / (D * (d.totient : ℝ)^2)) *
        (4 * Erdos821.Sieve.totientRatioAverageConstant * (harmonic K : ℝ)) + (K : ℝ) * E :=
      _root_.add_le_add (mul_le_mul_of_nonneg_left
        (Erdos821.Sieve.totient_ratio_two_mul_harmonic_average K) (by positivity)) le_rfl
    _ = _ := by dsimp [D, E]; ring

lemma rough_composite_progression_card_le_pairs (X K Y d : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d * K * Y) :
    (roughProgressionPrimes d Y X).card ≤
      ∑ k ∈ Finset.Icc 1 K, primePairCofactorCount X (d * k) := by
  let P : ℕ → Finset ℕ := fun k =>
    (Finset.range (X / (d * k) + 1)).filter (fun ℓ => ℓ.Prime ∧ (d * k * ℓ + 1).Prime)
  have hsub : roughProgressionPrimes d Y X ⊆
      (Finset.Icc 1 K).biUnion (fun k => (P k).image (fun ℓ => d * k * ℓ + 1)) := by
    intro p hp
    obtain ⟨hpX, hddvd, hpns⟩ := mem_filter.mp hp
    obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpX
    have hpred : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
    have hnot : ¬∀ ℓ, ℓ.Prime → ℓ ∣ p - 1 → ℓ < Y :=
      fun h => hpns (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hnot
    obtain ⟨ℓ, hℓ, hℓdvd, hYℓ⟩ := hnot
    let a := (p - 1) / ℓ
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hpred hℓdvd) hℓ.pos
    have haeq : a * ℓ = p - 1 := Nat.div_mul_cancel hℓdvd
    have hdℓ : d.Coprime ℓ := by
      apply (hℓ.coprime_iff_not_dvd.mpr ?_).symm
      intro h
      have := Nat.mem_smoothNumbers'.mp hdY ℓ hℓ h
      omega
    have hda : d ∣ a := hdℓ.dvd_of_dvd_mul_right (haeq ▸ hddvd)
    let k := a / d
    have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd ha hda) hd
    have hkd : d * k = a := Nat.mul_div_cancel' hda
    have hmul : d * k * ℓ = p - 1 := by rw [hkd, haeq]
    have hY : 0 < Y := by
      by_contra h
      have : Y = 0 := by omega
      rw [this, mul_zero] at hX
      omega
    have hkK : k ≤ K := by
      have hmul' : d * k * Y ≤ d * K * Y :=
        (Nat.mul_le_mul_left (d * k) hYℓ).trans (by omega)
      have hdk : d * k ≤ d * K := Nat.le_of_mul_le_mul_right hmul' hY
      exact Nat.le_of_mul_le_mul_left hdk hd
    have hℓX : ℓ ≤ X / (d * k) := (Nat.le_div_iff_mul_le (Nat.mul_pos hd hk)).mpr (by
      rw [mul_comm ℓ (d * k), hmul]
      omega)
    apply mem_biUnion.mpr
    refine ⟨k, mem_Icc.mpr ⟨hk, hkK⟩, mem_image.mpr ⟨ℓ, ?_, by omega⟩⟩
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega), hℓ, ?_⟩
    convert hprime using 1
    omega
  calc
    _ ≤ ((Finset.Icc 1 K).biUnion (fun k => (P k).image (fun ℓ => d * k * ℓ + 1))).card := card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((P k).image (fun ℓ => d * k * ℓ + 1)).card := card_biUnion_le
    _ ≤ _ := sum_le_sum (fun _ _ => card_image_le)

lemma rough_composite_progression_prime_count_le (X K Y J d : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d * K * Y)
    (hKX : d * K ≤ X) (hJ : 0 < J) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      (16 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * ((d : ℝ) / (d.totient : ℝ) ^ 2) +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  have hc : ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, (primePairCofactorCount X (d * k) : ℝ) := by
    exact_mod_cast rough_composite_progression_card_le_pairs X K Y d hd hdY hX
  exact hc.trans (sum_prime_pair_composite_cofactor_bound X K J d hd hKX hJ)

/-- A uniform bound close to one on the modulus/totient ratio preserves the
reciprocal-totient progression weight. -/
lemma rough_composite_progression_reciprocal_count_le (X K Y J d : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hX : X ≤ d * K * Y)
    (hKX : d * K ≤ X) (hJ : 0 < J) (hφd : d ≤ 2 * d.totient) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      (32 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (d.totient : ℝ)⁻¹ +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  apply (rough_composite_progression_prime_count_le X K Y J d hd hdY hX hKX hJ).trans
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφdR : (d : ℝ) ≤ 2 * d.totient := by exact_mod_cast hφd
  have hratio : (d : ℝ) / (d.totient : ℝ)^2 ≤ 2 * (d.totient : ℝ)⁻¹ := by
    apply (div_le_iff₀ (sq_pos_of_pos hφ)).mpr
    convert hφdR using 1
    field_simp
  have hH : 0 ≤ (harmonic K : ℝ) := harmonic_real_nonneg K
  have hC : 0 ≤ Erdos821.Sieve.totientRatioAverageConstant := by
    unfold Erdos821.Sieve.totientRatioAverageConstant
    positivity
  have hnonneg : 0 ≤ 16 * Erdos821.Sieve.totientRatioAverageConstant *
      (X : ℝ) * (harmonic K : ℝ) / ((J : ℝ) * Real.log 2)^2 := by positivity
  have h := mul_le_mul_of_nonneg_left hratio hnonneg
  calc
    _ ≤ (16 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (2 * (d.totient : ℝ)⁻¹) +
        (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) :=
      _root_.add_le_add h le_rfl
    _ = _ := by ring

/-- This bounds the rejected incidence sum, before any division by a
prime-incidence overcount. -/
theorem rough_composite_family_reciprocal_count_le (M : Finset ℕ) (D Q X K Y J : ℕ)
    (hM : ∀ d ∈ M, 0 < d ∧ D ≤ d ∧ d ≤ Q ∧
      d ∈ Nat.smoothNumbers Y ∧ d ≤ 2 * d.totient)
    (hX : X ≤ D * K * Y) (hKX : Q * K ≤ X) (hJ : 0 < J) :
    (∑ d ∈ M, ((roughProgressionPrimes d Y X).card : ℝ)) ≤
      (32 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (∑ d ∈ M, (d.totient : ℝ)⁻¹) +
      (M.card : ℝ) * K * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  have hb (d : ℕ) (hd : d ∈ M) := rough_composite_progression_reciprocal_count_le
    X K Y J d (hM d hd).1 (hM d hd).2.2.2.1
    (hX.trans (Nat.mul_le_mul_right Y (Nat.mul_le_mul_right K (hM d hd).2.1)))
    ((Nat.mul_le_mul_right K (hM d hd).2.2.1).trans hKX) hJ (hM d hd).2.2.2.2
  apply (sum_le_sum hb).trans_eq
  rw [sum_add_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  ring

end Erdos821.AnalyticSieve

namespace Erdos821

open AnalyticSieve

/-- The loss in replacing a product modulus by its totient tends to one,
with a bound depending explicitly on the smallest block-prime scale. -/
lemma prime_product_modulus_totient_ratio (r m d : ℕ)
    (hd : d ∈ primeProductModuli r m) :
    progressionScaleN m * d ≤ (progressionScaleN m + 2^r) * d.totient := by
  have hdp := primeProductModuli_properties hd
  have hdiv : d.properDivisors.card ≤ 2 ^ r := by
    calc
      _ ≤ d.divisors.card := Finset.card_le_card Nat.properDivisors_subset_divisors
      _ = _ := by rw [card_divisors_squarefree d hdp.2.1, hdp.2.2.1]
  have hsum : progressionScaleN m * (∑ c ∈ d.properDivisors, c.totient) ≤
      2 ^ r * d.totient := by
    calc
      _ = ∑ c ∈ d.properDivisors, progressionScaleN m * c.totient := mul_sum _ _ _
      _ ≤ ∑ _c ∈ d.properDivisors, d.totient :=
        sum_le_sum (fun c hc => prime_product_proper_divisor_totient r m d c hd hc)
      _ = d.properDivisors.card * d.totient := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hdiv
  have heq : d = d.totient + ∑ c ∈ d.properDivisors, c.totient := by
    calc
      d = ∑ c ∈ d.divisors, c.totient := (Nat.sum_totient d).symm
      _ = _ := by rw [← Nat.insert_self_properDivisors hdp.1.ne',
        sum_insert Nat.self_notMem_properDivisors]
  calc
    _ = progressionScaleN m * d.totient +
        progressionScaleN m * (∑ c ∈ d.properDivisors, c.totient) := by
      nth_rw 1 [heq]
      ring
    _ ≤ progressionScaleN m * d.totient + 2^r * d.totient := Nat.add_le_add_left hsum _
    _ = _ := by ring

lemma prime_product_modulus_le_twice_totient (r m d : ℕ)
    (hd : d ∈ primeProductModuli r m) (hm : 2^r ≤ progressionScaleN m) :
    d ≤ 2 * d.totient := by
  have h := (prime_product_modulus_totient_ratio r m d hd).trans
    (Nat.mul_le_mul_right d.totient (show progressionScaleN m + 2^r ≤
      2 * progressionScaleN m by omega))
  have h' : progressionScaleN m * d ≤ progressionScaleN m * (2 * d.totient) := by
    nlinarith only [h]
  exact Nat.le_of_mul_le_mul_left h' (by unfold progressionScaleN; positivity)

end Erdos821
