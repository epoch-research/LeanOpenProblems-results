import Submission.SmoothModulusSieveMass

/-!
# Primitive characters at smooth product moduli

At these squarefree moduli, whose prime factors all grow with the scale,
primitive characters constitute at least half of all characters once the
scale is sufficiently large. The quadratic cardinality obstruction to a
uniform large sieve therefore persists after restricting to primitive
characters. This does not address cancellation specific to prime sums.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

noncomputable def primitiveCharacters (d : ℕ) : Finset (DirichletCharacter ℂ d) :=
  Finset.univ.filter (fun χ => χ.IsPrimitive)

noncomputable def imprimitiveCharacters (d : ℕ) : Finset (DirichletCharacter ℂ d) :=
  Finset.univ.filter (fun χ => ¬χ.IsPrimitive)

lemma card_characters_factorsThrough_le {d c : ℕ} (hd : d ≠ 0) (hc : c ∣ d) :
    ((Finset.univ : Finset (DirichletCharacter ℂ d)).filter
      (fun χ => χ.FactorsThrough c)).card ≤ c.totient := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    exact hd (Nat.eq_zero_of_zero_dvd hc)
  letI : NeZero c := ⟨hc0⟩
  have hsub : (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
      (fun χ => χ.FactorsThrough c) ⊆
      (Finset.univ : Finset (DirichletCharacter ℂ c)).image (DirichletCharacter.changeLevel hc) := by
    intro χ hχ
    obtain ⟨hc', ψ, hψ⟩ := (Finset.mem_filter.mp hχ).2
    exact Finset.mem_image.mpr ⟨ψ, Finset.mem_univ _, hψ.symm⟩
  calc
    _ ≤ ((Finset.univ : Finset (DirichletCharacter ℂ c)).image
        (DirichletCharacter.changeLevel hc)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ c)).card := Finset.card_image_le
    _ = c.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

lemma imprimitiveCharacters_card_le_proper_divisor_totients (d : ℕ) (hd : d ≠ 0) :
    (imprimitiveCharacters d).card ≤ ∑ c ∈ d.properDivisors, c.totient := by
  have hsub : imprimitiveCharacters d ⊆ d.properDivisors.biUnion
      (fun c => (Finset.univ : Finset (DirichletCharacter ℂ d)).filter
        (fun χ => χ.FactorsThrough c)) := by
    intro χ hχ
    have hnp : ¬χ.IsPrimitive := (Finset.mem_filter.mp hχ).2
    have hcd := χ.conductor_dvd_level
    have hclt : χ.conductor < d := by
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hcd
      have hne : χ.conductor ≠ d := hnp
      omega
    exact Finset.mem_biUnion.mpr ⟨χ.conductor, Nat.mem_properDivisors.mpr ⟨hcd, hclt⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, χ.factorsThrough_conductor⟩⟩
  exact ((Finset.card_le_card hsub).trans Finset.card_biUnion_le).trans
    (Finset.sum_le_sum (fun c hc => card_characters_factorsThrough_le hd
      (Nat.mem_properDivisors.mp hc).1))

lemma primitiveCharacters_card_add_imprimitive (d : ℕ) (hd : d ≠ 0) :
    (primitiveCharacters d).card + (imprimitiveCharacters d).card = d.totient := by
  letI : NeZero d := ⟨hd⟩
  unfold primitiveCharacters imprimitiveCharacters
  rw [Finset.card_filter_add_card_filter_not, Finset.card_univ,
    ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

lemma prime_product_prime_factor_mem {r m d p : ℕ}
    (hd : d ∈ primeProductModuli r m) (hp : p ∈ d.primeFactors) :
    p ∈ geometricBlockPrimes m := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
  have hSP : S ⊆ geometricBlockPrimes m := (Finset.mem_powersetCard.mp hS).1
  have hprime : ∀ q ∈ S, q.Prime := fun q hq =>
    (mem_geometricBlockPrimes.mp (hSP hq)).1
  rw [Nat.primeFactors_prod hprime] at hp
  exact hSP hp

lemma prime_product_proper_divisor_totient (r m d c : ℕ)
    (hd : d ∈ primeProductModuli r m) (hc : c ∈ d.properDivisors) :
    progressionScaleN m * c.totient ≤ d.totient := by
  have hcd := (Nat.mem_properDivisors.mp hc).1
  have hdprops := primeProductModuli_properties hd
  have hco : 1 < d / c := Nat.one_lt_div_of_mem_properDivisors hc
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd (show d / c ≠ 1 by omega)
  have hpd : p ∣ d := hpc.trans (Nat.div_dvd_of_dvd hcd)
  have hpP := prime_product_prime_factor_mem hd (hp.mem_primeFactors hpd hdprops.1.ne')
  have hpN : progressionScaleN m ≤ p - 1 := by
    have h := (mem_geometricBlockPrimes.mp hpP).2.1
    omega
  have hφco : progressionScaleN m ≤ (d / c).totient := by
    calc
      _ ≤ p - 1 := hpN
      _ = p.totient := (Nat.totient_prime hp).symm
      _ ≤ _ := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd hpc)
  have hcop : c.Coprime (d / c) := by
    apply Nat.coprime_of_squarefree_mul
    rw [Nat.mul_div_cancel' hcd]
    exact hdprops.2.1
  calc
    _ ≤ (d / c).totient * c.totient := Nat.mul_le_mul_right _ hφco
    _ = d.totient := by rw [mul_comm, ← Nat.totient_mul hcop, Nat.mul_div_cancel' hcd]

lemma card_divisors_squarefree (d : ℕ) (hd : Squarefree d) :
    d.divisors.card = 2 ^ d.primeFactors.card := by
  rw [Nat.card_divisors hd.ne_zero]
  calc
    _ = ∏ _p ∈ d.primeFactors, (2 : ℕ) := Finset.prod_congr rfl (fun p hp => by
      rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)])
    _ = _ := Finset.prod_const _

lemma prime_product_imprimitive_card_bound (r m d : ℕ)
    (hd : d ∈ primeProductModuli r m) :
    progressionScaleN m * (imprimitiveCharacters d).card ≤ 2 ^ r * d.totient := by
  have hdprops := primeProductModuli_properties hd
  have hdiv : d.properDivisors.card ≤ 2 ^ r := by
    calc
      _ ≤ d.divisors.card := Finset.card_le_card Nat.properDivisors_subset_divisors
      _ = _ := by rw [card_divisors_squarefree d hdprops.2.1, hdprops.2.2.1]
  calc
    _ ≤ progressionScaleN m * ∑ c ∈ d.properDivisors, c.totient :=
      Nat.mul_le_mul_left _ (imprimitiveCharacters_card_le_proper_divisor_totients d hdprops.1.ne')
    _ = ∑ c ∈ d.properDivisors, progressionScaleN m * c.totient := Finset.mul_sum _ _ _
    _ ≤ ∑ _c ∈ d.properDivisors, d.totient :=
      Finset.sum_le_sum (fun c hc => prime_product_proper_divisor_totient r m d c hd hc)
    _ = d.properDivisors.card * d.totient := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hdiv

/-- The full-conductor characters are not a negligible part of these
families: they make up at least half of all characters at large scales. -/
theorem prime_product_totient_le_twice_primitive_card (r m d : ℕ)
    (hd : d ∈ primeProductModuli r m) (hm : 2 ^ (r + 1) ≤ progressionScaleN m) :
    d.totient ≤ 2 * (primitiveCharacters d).card := by
  have hbound := prime_product_imprimitive_card_bound r m d hd
  have hsum := primitiveCharacters_card_add_imprimitive d
    (primeProductModuli_properties hd).1.ne'
  have hm' : 2 * 2 ^ r ≤ progressionScaleN m := by simpa only [pow_succ, mul_comm] using hm
  have h : 2 ^ r * (2 * (imprimitiveCharacters d).card) ≤ 2 ^ r * d.totient := by
    calc
      _ = (2 * 2 ^ r) * (imprimitiveCharacters d).card := by ring
      _ ≤ progressionScaleN m * (imprimitiveCharacters d).card := Nat.mul_le_mul_right _ hm'
      _ ≤ _ := hbound
  have hcancel : 2 * (imprimitiveCharacters d).card ≤ d.totient :=
    Nat.le_of_mul_le_mul_left h (by positivity)
  omega

lemma prime_product_totient_mass_le_twice_primitive_mass (r m : ℕ)
    (hm : 2 ^ (r + 1) ≤ progressionScaleN m) :
    (∑ d ∈ primeProductModuli r m, d.totient) ≤
      2 * ∑ d ∈ primeProductModuli r m, (primitiveCharacters d).card := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun d hd => prime_product_totient_le_twice_primitive_card r m d hd hm)

/-- Primitive-character cardinality retains the quadratic modulus scale.
This statement does not estimate any twisted prime sum. -/
theorem eventually_prime_product_primitive_mass_power_lower (r k C : ℕ)
    (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∀ᶠ m : ℕ in atTop,
      C * 2 ^ (64 * r * (2 * k - 1) * m) ≤
        (∑ d ∈ primeProductModuli r m, (primitiveCharacters d).card) ^ k := by
  filter_upwards [eventually_prime_product_totient_mass_power_lower r k (2 ^ k * C) hr hk,
    eventually_ge_atTop (r + 1)] with m hm hmr
  have hm' : 2 ^ (r + 1) ≤ progressionScaleN m :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hmass := prime_product_totient_mass_le_twice_primitive_mass r m hm'
  have hpow := Nat.pow_le_pow_left hmass k
  rw [mul_pow] at hpow
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ k) _ (by positivity)
  calc
    _ = (2 ^ k * C) * 2 ^ (64 * r * (2 * k - 1) * m) := by ring
    _ ≤ _ := hm.trans hpow

/-- The weighted primitive-character energy used in the multiplicative
large sieve. No arithmetic restriction is imposed on the coefficients. -/
noncomputable def primitiveCharacterEnergy (D : Finset ℕ) (A : Finset ℤ)
    (a : ℤ → ℂ) : ℝ :=
  ∑ d ∈ D, ((d : ℝ) / d.totient) *
    ∑ χ ∈ primitiveCharacters d, ‖characterSum A a χ‖ ^ 2

lemma uniform_primitive_character_constant_lower (D : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (A : Finset ℤ) (hA : 1 ∈ A) (B : ℝ)
    (H : ∀ a : ℤ → ℂ, primitiveCharacterEnergy D A a ≤ B * ∑ n ∈ A, ‖a n‖ ^ 2) :
    (∑ d ∈ D, ((primitiveCharacters d).card : ℝ)) ≤ B := by
  have hsum (d : ℕ) (χ : DirichletCharacter ℂ d) :
      characterSum A (fun n => if n = 1 then 1 else 0) χ = 1 := by
    simp [characterSum, hA]
  have h := H (fun n => if n = 1 then 1 else 0)
  have he : (∑ n ∈ A, ‖(if n = 1 then (1 : ℂ) else 0)‖ ^ 2) = 1 := by
    calc
      _ = ∑ n ∈ A, if n = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        split_ifs <;> norm_num
      _ = 1 := by simp [hA]
  simp only [primitiveCharacterEnergy, hsum, norm_one, one_pow, Finset.sum_const,
    nsmul_eq_mul, mul_one, he] at h
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro d hd
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (hD d hd)
  have hw : (1 : ℝ) ≤ (d : ℝ) / d.totient := by
    apply (le_div_iff₀ hφ).mpr
    simpa only [one_mul] using (show (d.totient : ℝ) ≤ d by exact_mod_cast Nat.totient_le d)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw
    (Nat.cast_nonneg (α := ℝ) (primitiveCharacters d).card)

/-- The full-conductor restriction does not remove the quadratic cardinality
cost in a coefficient-uniform multiplicative large-sieve estimate. -/
theorem prime_product_uniform_primitive_constant_lower (r m : ℕ)
    (hsmall : 4096 * r * (m + 1) ≤ progressionScaleN m)
    (hm : 2 ^ (r + 1) ≤ progressionScaleN m)
    (A : Finset ℤ) (hA : 1 ∈ A) (B : ℝ)
    (H : ∀ a : ℤ → ℂ, primitiveCharacterEnergy (primeProductModuli r m) A a ≤
      B * ∑ n ∈ A, ‖a n‖ ^ 2) :
    (2 : ℝ) ^ (128 * r * m) ≤
      2 * ((4096 : ℝ) ^ r * r.factorial * ((m : ℝ) + 1) ^ r) * B := by
  have hmass := prime_product_totient_mass_le_twice_primitive_mass r m hm
  have hnat : 2 ^ (128 * r * m) ≤
      (2 * (4096 ^ r * r.factorial * (m + 1) ^ r)) *
        ∑ d ∈ primeProductModuli r m, (primitiveCharacters d).card := by
    calc
      _ ≤ _ := prime_product_totient_mass_lower r m hsmall
      _ ≤ (4096 ^ r * r.factorial * (m + 1) ^ r) *
          (2 * ∑ d ∈ primeProductModuli r m, (primitiveCharacters d).card) :=
        Nat.mul_le_mul_left _ hmass
      _ = _ := by ring
  have hlo : (2 : ℝ) ^ (128 * r * m) ≤
      2 * ((4096 : ℝ) ^ r * r.factorial * ((m : ℝ) + 1) ^ r) *
        ∑ d ∈ primeProductModuli r m, ((primitiveCharacters d).card : ℝ) := by
    exact_mod_cast hnat
  exact hlo.trans (mul_le_mul_of_nonneg_left
    (uniform_primitive_character_constant_lower _
      (fun d hd => (primeProductModuli_properties hd).1) A hA B H) (by positivity))

end Erdos821
