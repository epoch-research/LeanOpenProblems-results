import FormalConjecturesUtil

/-!
# A quantitative bound for gaps between integers avoiding finite prime sets

Auxiliary work for Erdős 972. This only bounds finite-modulus obstructions;
it does not assert simultaneous primality.
-/

namespace Explore972

open Finset

lemma multiples_interval_error (a b d : ℤ) (hab : a ≤ b) (hd : 0 < d) :
    |(#{x ∈ Ico a b | d ∣ x} : ℚ) - ((b - a : ℤ) : ℚ) / d| ≤ 1 := by
  have hdr : (0 : ℚ) < d := by exact_mod_cast hd
  have hceil : ⌈a / (d : ℚ)⌉ ≤ ⌈b / (d : ℚ)⌉ := by
    apply Int.ceil_mono
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hdr.le
  have hc := Int.Ico_filter_dvd_card a b hd
  rw [max_eq_left (sub_nonneg.mpr hceil)] at hc
  have hcq : (#{x ∈ Ico a b | d ∣ x} : ℚ) =
      (⌈b / (d : ℚ)⌉ : ℚ) - (⌈a / (d : ℚ)⌉ : ℚ) := by exact_mod_cast hc
  rw [hcq]
  have he : ((b - a : ℤ) : ℚ) / d = (b : ℚ) / d - (a : ℚ) / d := by
    push_cast
    ring
  rw [he]
  apply abs_le.mpr
  constructor
  · linarith [Int.le_ceil (b / (d : ℚ)), Int.ceil_lt_add_one (a / (d : ℚ))]
  · linarith [Int.le_ceil (a / (d : ℚ)), Int.ceil_lt_add_one (b / (d : ℚ))]

lemma prime_prod_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (x : ℤ) :
    (∏ p ∈ S, (p : ℤ)) ∣ x ↔ ∀ p ∈ S, (p : ℤ) ∣ x := by
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_coprime _ h
    intro p hp q hq hpq
    exact_mod_cast (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq

lemma prime_prod_indicator (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (x : ℤ) :
    (∏ p ∈ S, if (p : ℤ) ∣ x then (1 : ℚ) else 0) =
      if (∏ p ∈ S, (p : ℤ)) ∣ x then 1 else 0 := by
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one]
  simp only [prime_prod_dvd_iff S hS]

noncomputable def siftMass (S : Finset ℕ) (a b : ℤ) : ℚ :=
  ∑ x ∈ Ico a b, ∏ p ∈ S, (1 - if (p : ℤ) ∣ x then 1 else 0)

noncomputable def sieveDensity (S : Finset ℕ) : ℚ :=
  ∏ p ∈ S, (1 - 1 / (p : ℚ))

lemma siftMass_expansion (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a b : ℤ) :
    siftMass S a b = ∑ T ∈ S.powerset,
      (-1 : ℚ) ^ T.card * (#{x ∈ Ico a b | (∏ p ∈ T, (p : ℤ)) ∣ x} : ℚ) := by
  unfold siftMass
  simp_rw [Finset.prod_sub]
  simp only [prod_const_one, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  have hTS : T ⊆ S := mem_powerset.mp hT
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [prime_prod_indicator T (fun p hp => hS p (hTS hp))]
  simp

lemma sieveDensity_expansion (S : Finset ℕ) :
    sieveDensity S = ∑ T ∈ S.powerset,
      (-1 : ℚ) ^ T.card / ((∏ p ∈ T, (p : ℤ)) : ℚ) := by
  unfold sieveDensity
  rw [Finset.prod_sub]
  simp [div_eq_mul_inv]

set_option maxHeartbeats 2000000 in
lemma siftMass_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a b : ℤ) (hab : a ≤ b) :
    |siftMass S a b - ((b - a : ℤ) : ℚ) * sieveDensity S| ≤ (2 : ℚ) ^ S.card := by
  classical
  let d : Finset ℕ → ℤ := fun T => ∏ p ∈ T, (p : ℤ)
  let c : Finset ℕ → ℚ := fun T => (#{x ∈ Ico a b | d T ∣ x} : ℚ)
  let L : ℚ := ((b - a : ℤ) : ℚ)
  have hexp : siftMass S a b = ∑ T ∈ S.powerset, (-1 : ℚ) ^ T.card * c T :=
    siftMass_expansion S hS a b
  have hden : sieveDensity S = ∑ T ∈ S.powerset, (-1 : ℚ) ^ T.card / d T := by
    simpa only [d, Int.cast_prod, Int.cast_natCast] using sieveDensity_expansion S
  have hbound : ∀ T ∈ S.powerset, |c T - L / d T| ≤ 1 := by
    intro T hT
    apply multiples_interval_error a b _ hab
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hS p (mem_powerset.mp hT hp)).pos
  change |siftMass S a b - L * sieveDensity S| ≤ _
  calc
    _ = |∑ T ∈ S.powerset, (-1 : ℚ) ^ T.card * (c T - L / d T)| := by
      rw [hexp, hden, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ ≤ ∑ T ∈ S.powerset, |(-1 : ℚ) ^ T.card * (c T - L / d T)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S.powerset, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro T hT
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hbound T hT
    _ = (2 : ℚ) ^ S.card := by simp

lemma sieveDensity_lower (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (1 / 2 : ℚ) ^ S.card ≤ sieveDensity S := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    norm_num
  · intro p hp
    have hpr : (2 : ℚ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have hp0 : (0 : ℚ) < p := by linarith
    have hdiv : (1 : ℚ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpr
    linarith

/-- A crude Jacobsthal-type bound. For `k` prime divisors, every `4^k + 1`
consecutive integers contain an integer avoiding all of them. -/
theorem exists_avoiding_primes_in_interval (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a : ℤ) :
    ∃ x : ℤ, a ≤ x ∧ x < a + (4 : ℤ) ^ S.card + 1 ∧ ∀ p ∈ S, ¬ (p : ℤ) ∣ x := by
  let b : ℤ := a + (4 : ℤ) ^ S.card + 1
  have hab : a ≤ b := by
    dsimp [b]
    have hpow := pow_nonneg (by norm_num : (0 : ℤ) ≤ 4) S.card
    omega
  have herr := (abs_le.mp (siftMass_error S hS a b hab)).1
  have hlow := sieveDensity_lower S hS
  have hlength : ((b - a : ℤ) : ℚ) = (4 : ℚ) ^ S.card + 1 := by
    dsimp [b]
    push_cast
    ring
  rw [hlength] at herr
  have hpow : (4 : ℚ) ^ S.card * (1 / 2 : ℚ) ^ S.card = (2 : ℚ) ^ S.card := by
    rw [← mul_pow]
    norm_num
  have hpos : 0 < (1 / 2 : ℚ) ^ S.card := by positivity
  have hmass : 0 < siftMass S a b := by
    nlinarith [mul_le_mul_of_nonneg_left hlow
      (show (0 : ℚ) ≤ (4 : ℚ) ^ S.card + 1 by positivity)]
  by_contra h
  push_neg at h
  have hz : siftMass S a b = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Finset.mem_Ico.mp hx
    obtain ⟨p, hp, hpx⟩ := h x hx'.1 hx'.2
    exact Finset.prod_eq_zero hp (by simp [hpx])
  linarith

/-- The interval bound grows slower than a fixed power of the modulus. The
constant is deliberately very crude; small prime factors are absorbed into it. -/
lemma fourth_power_prime_factor_bound (n : ℕ) (hn : 0 < n) :
    ((4 : ℕ) ^ n.primeFactors.card) ^ 4 ≤ (256 : ℕ) ^ 256 * n := by
  let S := n.primeFactors.filter (fun p => p < 256)
  let T := n.primeFactors.filter (fun p => ¬ p < 256)
  have hcard : S.card + T.card = n.primeFactors.card :=
    Finset.card_filter_add_card_filter_not (s := n.primeFactors) (fun p => p < 256)
  have hS : S.card ≤ 256 := by
    calc
      S.card ≤ (Finset.range 256).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = 256 := Finset.card_range _
  have hT : (256 : ℕ) ^ T.card ≤ ∏ p ∈ T, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro p hp
      omega
    · intro p hp
      have := (Finset.mem_filter.mp hp).2
      omega
  have hprod : ∏ p ∈ T, p ≤ n := by
    apply Nat.le_of_dvd hn
    exact (Finset.prod_dvd_prod_of_subset T n.primeFactors id
      (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
  calc
    ((4 : ℕ) ^ n.primeFactors.card) ^ 4 = (256 : ℕ) ^ n.primeFactors.card := by
      rw [← pow_mul, Nat.mul_comm n.primeFactors.card 4, pow_mul]
      norm_num
    _ = (256 : ℕ) ^ S.card * 256 ^ T.card := by rw [← hcard, pow_add]
    _ ≤ (256 : ℕ) ^ 256 * n := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) hS) (hT.trans hprod)

/-- Every integer interval of the stated length contains an integer coprime
to the prescribed positive modulus. -/
theorem exists_coprime_in_interval (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ∃ x : ℤ, a ≤ x ∧ x < a + (4 : ℤ) ^ n.primeFactors.card + 1 ∧ IsCoprime x (n : ℤ) := by
  obtain ⟨x, hxlo, hxhi, hx⟩ := exists_avoiding_primes_in_interval n.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) a
  refine ⟨x, hxlo, hxhi, ?_⟩
  apply Int.isCoprime_iff_nat_coprime.mpr
  simp only [Int.natAbs_natCast]
  by_contra h
  obtain ⟨p, hp, hpx, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hx p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩) (Int.natCast_dvd.mpr hpx)

/-- A real-endpoint version, with one additional unit of slack. -/
theorem exists_coprime_in_real_interval (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∃ k : ℤ, x ≤ k ∧ (k : ℝ) < x + (4 : ℝ) ^ n.primeFactors.card + 2 ∧
      IsCoprime k (n : ℤ) := by
  obtain ⟨k, hklo, hkhi, hkc⟩ := exists_coprime_in_interval n hn ⌈x⌉
  have hklo' : (⌈x⌉ : ℝ) ≤ k := by exact_mod_cast hklo
  have hkhi' : (k : ℝ) < (⌈x⌉ : ℝ) + (4 : ℝ) ^ n.primeFactors.card + 1 := by
    exact_mod_cast hkhi
  refine ⟨k, (Int.le_ceil x).trans hklo', ?_, hkc⟩
  linarith [Int.ceil_lt_add_one x]

#print axioms exists_coprime_in_real_interval


#print axioms fourth_power_prime_factor_bound
#print axioms exists_coprime_in_interval


#print axioms exists_avoiding_primes_in_interval

end Explore972
