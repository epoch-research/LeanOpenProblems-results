import Submission.SmoothCompositeModuli

/-!
# Close reduced fractions at smooth product moduli

Smoothness of the moduli does not by itself improve the minimum separation
used by the elementary large sieve. Two coprime moduli d,e have reduced
fractions separated by exactly 1/(d*e). The constructed smooth product family
contains such pairs at the full product scale.

This is an audit of one possible shortcut, not an upper bound on the quality
of every large-sieve or dispersion estimate, and not a disproof of Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

lemma exists_reduced_fractions_exact_gap (d e : ℕ) (hd : 1 < d) (he : 1 < e)
    (hde : d.Coprime e) :
    ∃ a b : ℕ, 0 < a ∧ a < d ∧ a.Coprime d ∧
      0 < b ∧ b < e ∧ b.Coprime e ∧
      |(a : ℝ) / d - (b : ℝ) / e| = 1 / ((d : ℝ) * e) := by
  obtain ⟨a, had, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hde.symm hd
  let b := e * a / d
  have heq : e * a = d * b + 1 := by
    have h := Nat.mod_add_div (e * a) d
    rw [ha] at h
    dsimp [b]
    omega
  have ha0 : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    simp only [ha0, mul_zero, Nat.zero_mod] at ha
    omega
  have hb0 : 0 < b := by
    have hea : e ≤ e * a := by
      simpa only [mul_one] using Nat.mul_le_mul_left e (show 1 ≤ a from ha0)
    nlinarith only [heq, hea, he]
  have hbe : b < e := by
    have hmul : e * a < e * d := Nat.mul_lt_mul_of_pos_left had (by omega)
    nlinarith only [heq, hmul, hd]
  have hac : a.Coprime d := by
    apply Nat.coprime_of_mul_modEq_one e
    change (a * e) % d = 1 % d
    rw [mul_comm, ha, Nat.mod_eq_of_lt hd]
  have hbc : b.Coprime e := by
    have hleft : Nat.gcd b e ∣ e * a := dvd_mul_of_dvd_left (Nat.gcd_dvd_right b e) a
    have hright : Nat.gcd b e ∣ d * b := dvd_mul_of_dvd_right (Nat.gcd_dvd_left b e) d
    rw [heq] at hleft
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hright).mp hleft)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have heqR : (e : ℝ) * a = d * b + 1 := by exact_mod_cast heq
  have hdiff : (a : ℝ) / d - (b : ℝ) / e = 1 / ((d : ℝ) * e) := by
    field_simp
    nlinarith only [heqR]
  exact ⟨a, b, ha0, had, hac, hb0, hbe, hbc, by rw [hdiff, abs_of_pos (by positivity)]⟩

lemma exists_coprime_prime_product_moduli (r m : ℕ) (hr : 1 ≤ r)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m) :
    ∃ d ∈ primeProductModuli r m, ∃ e ∈ primeProductModuli r m,
      1 < d ∧ 1 < e ∧ d.Coprime e := by
  let P := geometricBlockPrimes m
  have hc : progressionScaleN m ≤ 2048 * (m + 1) * P.card := geometric_block_prime_count m
  have hPcard : 2 * r ≤ P.card := by nlinarith
  obtain ⟨S, hSP, hSc⟩ := Finset.exists_subset_card_eq (show r ≤ P.card by omega)
  have hdiff : r ≤ (P \ S).card := by rw [Finset.card_sdiff_of_subset hSP, hSc]; omega
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq hdiff
  have hTP : T ⊆ P := hTS.trans Finset.sdiff_subset
  let d := ∏ p ∈ S, p
  let e := ∏ p ∈ T, p
  have hd : d ∈ primeProductModuli r m :=
    Finset.mem_image.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨hSP, hSc⟩, rfl⟩
  have he : e ∈ primeProductModuli r m :=
    Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hTP, hTc⟩, rfl⟩
  have hdprops := primeProductModuli_properties hd
  have heprops := primeProductModuli_properties he
  have hd1 : 1 < d := by
    by_contra h
    have hdEq : d = 1 := by omega
    have hc := hdprops.2.2.1
    simp only [hdEq, Nat.primeFactors_one, Finset.card_empty] at hc
    omega
  have he1 : 1 < e := by
    by_contra h
    have heEq : e = 1 := by omega
    have hc := heprops.2.2.1
    simp only [heEq, Nat.primeFactors_one, Finset.card_empty] at hc
    omega
  refine ⟨d, hd, e, he, hd1, he1, ?_⟩
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  apply (Nat.coprime_primes (mem_geometricBlockPrimes.mp (hSP hp)).1
    (mem_geometricBlockPrimes.mp (hTP hq)).1).mpr
  intro hpq
  exact (Finset.mem_sdiff.mp (hTS hq)).2 (hpq ▸ hp)

/-- The family has distinct reduced fractions at reciprocal-product-square
spacing. Sparsity in its modulus support cannot be used to assume that all
these fractions have a larger minimum separation. -/
theorem exists_close_fractions_at_prime_product_moduli (r m : ℕ) (hr : 1 ≤ r)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m) :
    ∃ d ∈ primeProductModuli r m, ∃ e ∈ primeProductModuli r m,
      d ≠ e ∧ ∃ a b : ℕ, 0 < a ∧ a < d ∧ a.Coprime d ∧
        0 < b ∧ b < e ∧ b.Coprime e ∧
        0 < |(a : ℝ) / d - (b : ℝ) / e| ∧
        |(a : ℝ) / d - (b : ℝ) / e| ≤ 1 / (2 : ℝ) ^ (128 * r * m) := by
  obtain ⟨d, hd, e, he, hd1, he1, hde⟩ := exists_coprime_prime_product_moduli r m hr hsmall
  obtain ⟨a, b, ha0, had, hac, hb0, hbe, hbc, hgap⟩ :=
    exists_reduced_fractions_exact_gap d e hd1 he1 hde
  have hne : d ≠ e := by
    intro h
    have h' := hde
    rw [h, Nat.coprime_self] at h'
    omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  refine ⟨d, hd, e, he, hne, a, b, ha0, had, hac, hb0, hbe, hbc, ?_, ?_⟩
  · rw [hgap]
    positivity
  · rw [hgap]
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ (128 * r * m))
    have hdlo := (primeProductModuli_properties hd).2.2.2.1
    have helo := (primeProductModuli_properties he).2.2.2.1
    have hprod : 2 ^ (128 * r * m) ≤ d * e := by
      calc
        _ = (progressionScaleN m) ^ r * (progressionScaleN m) ^ r := by
          simp only [progressionScaleN, ← pow_mul, ← pow_add]
          congr 1
          ring
        _ ≤ _ := Nat.mul_le_mul hdlo helo
    exact_mod_cast hprod

/-- Any separation bound valid for all reduced fractions at these product
moduli is at most the reciprocal square of their lower product scale. -/
theorem prime_product_uniform_separation_le (r m : ℕ) (hr : 1 ≤ r)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m) (δ : ℝ)
    (hsep : ∀ d ∈ primeProductModuli r m, ∀ e ∈ primeProductModuli r m, d ≠ e →
      ∀ a b : ℕ, a < d → a.Coprime d → b < e → b.Coprime e →
        δ ≤ |(a : ℝ) / d - (b : ℝ) / e|) :
    δ ≤ 1 / (2 : ℝ) ^ (128 * r * m) := by
  obtain ⟨d, hd, e, he, hde, a, b, _, had, hac, _, hbe, hbc, _, hgap⟩ :=
    exists_close_fractions_at_prime_product_moduli r m hr hsmall
  exact (hsep d hd e he hde a b had hac hbe hbc).trans hgap

/-- The finite size condition holds at every sufficiently large scale for
any fixed positive number of prime factors. -/
theorem eventually_prime_product_uniform_separation_le (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ m : ℕ in atTop, ∀ δ : ℝ,
      (∀ d ∈ primeProductModuli r m, ∀ e ∈ primeProductModuli r m, d ≠ e →
        ∀ a b : ℕ, a < d → a.Coprime d → b < e → b.Coprime e →
          δ ≤ |(a : ℝ) / d - (b : ℝ) / e|) →
      δ ≤ 1 / (2 : ℝ) ^ (128 * r * m) := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (4096 * r) 1] with m hm
  intro δ hsep
  have hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m := by
    have h : 4096 * r * (m + 1) ≤ 2 ^ m := by simpa only [one_mul, pow_one] using hm
    exact h.trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact prime_product_uniform_separation_le r m hr hsmall δ hsep

end Erdos821
