import Submission.LargePrimeMoments

/-!
# Divisor switching for the exact large-prime-factor moments

The factorial moments are rewritten as progression sums at products of
large primes, and then as prime values with short cofactors. These are
identities, not estimates for the resulting prime correlations.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

set_option maxHeartbeats 2000000

noncomputable def largePrimeBasis (Y N : ℕ) : Finset ℕ :=
  (N + 1).primesBelow.filter (fun q => Y ≤ q)

noncomputable def largePrimeProducts (Y N j : ℕ) : Finset ℕ :=
  ((largePrimeBasis Y N).powersetCard j).image (fun S => ∏ q ∈ S, q)

lemma mem_largePrimeBasis {Y N q : ℕ} :
    q ∈ largePrimeBasis Y N ↔ q.Prime ∧ Y ≤ q ∧ q ≤ N := by
  simp only [largePrimeBasis, mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hqN, hprime⟩, hYq⟩
    exact ⟨hprime, hYq, by omega⟩
  · rintro ⟨hprime, hYq, hqN⟩
    exact ⟨⟨by omega, hprime⟩, hYq⟩

lemma large_prime_product_divisor_count (Y N n j : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    ((largePrimeProducts Y N j).filter (fun a => a ∣ n)).card =
      (largePrimeDivisors Y n).card.choose j := by
  have hfilter : ((largePrimeBasis Y N).powersetCard j).filter
      (fun S => (∏ q ∈ S, q) ∣ n) = (largePrimeDivisors Y n).powersetCard j := by
    ext S
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP, hSj⟩, hprod⟩
      refine ⟨?_, hSj⟩
      intro q hq
      have hqP := mem_largePrimeBasis.mp (hSP hq)
      have hqn := (dvd_prod_of_mem _root_.id hq).trans hprod
      exact mem_filter.mpr ⟨hqP.1.mem_primeFactors hqn hn.ne', hqP.2.1⟩
    · rintro ⟨hSL, hSj⟩
      have hSP : S ⊆ largePrimeBasis Y N := by
        intro q hq
        obtain ⟨hqn, hYq⟩ := mem_filter.mp (hSL hq)
        exact mem_largePrimeBasis.mpr ⟨Nat.prime_of_mem_primeFactors hqn, hYq,
          (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hqn)).trans hnN⟩
      refine ⟨⟨hSP, hSj⟩, ?_⟩
      exact (Sieve.prod_primes_dvd_iff S (fun q hq => (mem_largePrimeBasis.mp (hSP hq)).1) n).mpr
        (fun q hq => Nat.dvd_of_mem_primeFactors (mem_filter.mp (hSL hq)).1)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ q ∈ S, q)
      (↑((largePrimeDivisors Y n).powersetCard j) : Set (Finset ℕ)) := by
    intro S hS T hT heq
    change S ∈ (largePrimeDivisors Y n).powersetCard j at hS
    change T ∈ (largePrimeDivisors Y n).powersetCard j at hT
    have hSL : S ⊆ largePrimeDivisors Y n := (mem_powersetCard.mp hS).1
    have hTL : T ⊆ largePrimeDivisors Y n := (mem_powersetCard.mp hT).1
    have hprS : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (mem_filter.mp (hSL hq)).1
    have hprT : ∀ q ∈ T, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (mem_filter.mp (hTL hq)).1
    have h := congrArg Nat.primeFactors heq
    simpa only [Nat.primeFactors_prod hprS, Nat.primeFactors_prod hprT] using h
  unfold largePrimeProducts
  rw [filter_image, hfilter, Finset.card_image_of_injOn hinj, card_powersetCard]

lemma largePrimeProducts_pos {Y N j a : ℕ} (ha : a ∈ largePrimeProducts Y N j) : 0 < a := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
  exact prod_pos (fun q hq => (mem_largePrimeBasis.mp ((mem_powersetCard.mp hS).1 hq)).1.pos)

lemma largePrimeProducts_lower {Y N j a : ℕ} (ha : a ∈ largePrimeProducts Y N j) : Y^j ≤ a := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
  calc
    _ = ∏ _q ∈ S, Y := by rw [prod_const, (mem_powersetCard.mp hS).2]
    _ ≤ _ := prod_le_prod' (fun q hq => (mem_largePrimeBasis.mp ((mem_powersetCard.mp hS).1 hq)).2.1)

lemma smooth_coprime_largePrimeProducts {Y N j d a : ℕ}
    (hd : d ∈ Nat.smoothNumbers Y) (ha : a ∈ largePrimeProducts Y N j) : d.Coprime a := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  have hqP := mem_largePrimeBasis.mp ((mem_powersetCard.mp hS).1 hq)
  apply (hqP.1.coprime_iff_not_dvd.mpr ?_).symm
  intro hqd
  have hlt := Nat.mem_smoothNumbers'.mp hd q hqP.1 hqd
  omega

/-- The moment is an exact sum over squarefree products of j large prime
factors. No prime-factor incidences are discarded. -/
theorem largePrimeMoment_eq_product_sum (P : Finset ℕ) (w : ℕ → ℝ) (Y N j : ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ N) :
    largePrimeMoment P w Y j =
      ∑ a ∈ largePrimeProducts Y N j, ∑ p ∈ P.filter (fun p => a ∣ p - 1), w p := by
  simp_rw [sum_filter]
  rw [sum_comm]
  unfold largePrimeMoment
  apply sum_congr rfl
  intro p hp
  have hcount := large_prime_product_divisor_count Y N (p - 1) j (by have := (hP p hp).1; omega)
    (by have := (hP p hp).2; omega)
  rw [← sum_filter, sum_const, nsmul_eq_mul, hcount, mul_comm]

/-- A smooth progression modulus is coprime to every selected large-prime
product, so the two divisibility conditions combine without correction. -/
theorem largePrimeMoment_progression_eq (d Y N j : ℕ) (w : ℕ → ℝ)
    (hd : d ∈ Nat.smoothNumbers Y) :
    largePrimeMoment ((N + 1).primesBelow.filter (fun p => d ∣ p - 1)) w Y j =
      ∑ a ∈ largePrimeProducts Y N j,
        ∑ p ∈ (N + 1).primesBelow.filter (fun p => d * a ∣ p - 1), w p := by
  rw [largePrimeMoment_eq_product_sum _ w Y N j (by
    intro p hp
    have h := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
    exact ⟨h.2.two_le, by have hpN := h.1; have hp2 := h.2.two_le; omega⟩)]
  apply sum_congr rfl
  intro a ha
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hp, hdp⟩, hap⟩
    exact ⟨hp, (smooth_coprime_largePrimeProducts hd ha).mul_dvd_of_dvd_of_dvd hdp hap⟩
  · rintro ⟨hp, hda⟩
    exact ⟨⟨hp, (dvd_mul_right d a).trans hda⟩, (dvd_mul_left a d).trans hda⟩

noncomputable def shiftedPrimeCofactors (N q : ℕ) : Finset ℕ :=
  (Icc 1 ((N - 1) / q)).filter (fun k => (q * k + 1).Prime)

/-- Exact divisor switching, including the endpoint p<=N and the prime 2. -/
theorem prime_progression_weight_eq_cofactors (N q : ℕ) (hq : 0 < q) (w : ℕ → ℝ) :
    (∑ p ∈ (N + 1).primesBelow.filter (fun p => q ∣ p - 1), w p) =
      ∑ k ∈ shiftedPrimeCofactors N q, w (q * k + 1) := by
  apply sum_bij (fun p _ => (p - 1) / q)
  · intro p hp
    obtain ⟨hpN, hqd⟩ := mem_filter.mp hp
    obtain ⟨hpN, hprime⟩ := Nat.mem_primesBelow.mp hpN
    have hn : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
    have hk : 0 < (p - 1) / q := Nat.div_pos (Nat.le_of_dvd hn hqd) hq
    have hmul : q * ((p - 1) / q) = p - 1 := Nat.mul_div_cancel' hqd
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk, ?_⟩, ?_⟩
    · exact Nat.div_le_div_right (by omega : p - 1 ≤ N - 1)
    · rw [hmul, Nat.sub_add_cancel hprime.pos]
      exact hprime
  · intro p hp p' hp' heq
    have hd := (mem_filter.mp hp).2
    have hd' := (mem_filter.mp hp').2
    have hmul := Nat.mul_div_cancel' hd
    have hmul' := Nat.mul_div_cancel' hd'
    have heqmul := congrArg (fun k : ℕ => q * k) heq
    dsimp only at heqmul
    rw [hmul, hmul'] at heqmul
    have hp2 := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2.two_le
    have hp2' := (Nat.mem_primesBelow.mp (mem_filter.mp hp').1).2.two_le
    omega
  · intro k hk
    obtain ⟨hkI, hprime⟩ := mem_filter.mp hk
    have hk0 := (mem_Icc.mp hkI).1
    have hkN := (mem_Icc.mp hkI).2
    have hmul : q * k ≤ N - 1 := by
      have h := (Nat.le_div_iff_mul_le hq).mp hkN
      simpa only [mul_comm] using h
    have hN : 0 < N := by
      have hqk : 0 < q * k := Nat.mul_pos hq hk0
      omega
    refine ⟨q * k + 1, mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩, ?_⟩, ?_⟩
    · simp only [Nat.add_sub_cancel]
      exact dvd_mul_right q k
    · simp only [Nat.add_sub_cancel, Nat.mul_div_cancel_left k hq]
  · intro p hp
    have hpd := (mem_filter.mp hp).2
    have hp0 := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2.pos
    rw [Nat.mul_div_cancel' hpd, Nat.sub_add_cancel hp0]

/-- The higher moments become correlations of several large primes with a
prime of the form d*a*k+1. Establishing lower bounds for these correlations
is a separate analytic problem. -/
theorem largePrimeMoment_progression_eq_cofactors (d Y N j : ℕ) (w : ℕ → ℝ)
    (hd : d ∈ Nat.smoothNumbers Y) :
    largePrimeMoment ((N + 1).primesBelow.filter (fun p => d ∣ p - 1)) w Y j =
      ∑ a ∈ largePrimeProducts Y N j,
        ∑ k ∈ shiftedPrimeCofactors N (d * a), w (d * a * k + 1) := by
  rw [largePrimeMoment_progression_eq d Y N j w hd]
  apply sum_congr rfl
  intro a ha
  exact prime_progression_weight_eq_cofactors N (d * a)
    (Nat.mul_pos (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hd)) (largePrimeProducts_pos ha)) w

lemma largePrimeProducts_one (Y N : ℕ) : largePrimeProducts Y N 1 = largePrimeBasis Y N := by
  ext a
  constructor
  · intro ha
    obtain ⟨S, hS, haS⟩ := mem_image.mp ha
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (mem_powersetCard.mp hS).2
    subst S
    simp only [prod_singleton] at haS
    subst a
    exact (mem_powersetCard.mp hS).1 (mem_singleton_self q)
  · intro ha
    apply mem_image.mpr
    refine ⟨{a}, mem_powersetCard.mpr ⟨?_, by simp⟩, by simp⟩
    exact singleton_subset_iff.mpr ha

lemma large_prime_selected_cofactor_le (d Y N j a k : ℕ) (hd : 0 < d) (hY : 1 ≤ Y)
    (ha : a ∈ largePrimeProducts Y N j) (hk : k ∈ shiftedPrimeCofactors N (d * a)) :
    k ≤ (N - 1) / (d * Y^j) := by
  have hda : 0 < d * a := Nat.mul_pos hd (largePrimeProducts_pos ha)
  have hkN := (mem_Icc.mp (mem_filter.mp hk).1).2
  have hmul : d * a * k ≤ N - 1 := by
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hda).mp hkN
  have hlow := Nat.mul_le_mul_right k (Nat.mul_le_mul_left d (largePrimeProducts_lower ha))
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos hd (Nat.pow_pos (by omega : 0 < Y)))).mpr
  simpa only [mul_comm k (d * Y^j)] using hlow.trans hmul

/-- A fixed finite cofactor expansion of the smooth progression weight. -/
theorem smooth_progression_weight_eq_switched_moments (d Y N s : ℕ) (w : ℕ → ℝ)
    (hY : 1 ≤ Y) (hd : d ∈ Nat.smoothNumbers Y) (hN : N ≤ d * Y^(s + 1)) :
    (∑ p ∈ ((N + 1).primesBelow.filter (fun p => d ∣ p - 1)).filter
      (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) =
      ∑ j ∈ range (s + 1), (-1 : ℝ)^j *
        (∑ a ∈ largePrimeProducts Y N j,
          ∑ k ∈ shiftedPrimeCofactors N (d * a), w (d * a * k + 1)) := by
  have hP (p : ℕ) (hp : p ∈ (N + 1).primesBelow.filter (fun p => d ∣ p - 1)) :
      2 ≤ p ∧ p - 1 < d * Y^(s + 1) := by
    have h := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
    exact ⟨h.2.two_le, by have hpN := h.1; have hp2 := h.2.two_le; omega⟩
  rw [smooth_prime_weight_eq_large_moments _ w Y s (fun p hp => (hP p hp).1) (by
    intro p hp
    have h := largePrimeDivisors_card_lt_of_smooth_divisor Y (p - 1) d (s + 1) hY
      (by have := (hP p hp).1; omega) hd (mem_filter.mp hp).2 (hP p hp).2
    omega)]
  unfold largePrimeSievePartial
  apply sum_congr rfl
  intro j hj
  rw [largePrimeMoment_progression_eq_cofactors d Y N j w hd]

/-- When the remaining cofactor is smaller than Y^2, there is at most one
large prime factor. The subtraction below is then exact, not a union bound. -/
theorem smooth_progression_weight_eq_sub_large_pairs (d Y N : ℕ) (w : ℕ → ℝ)
    (hY : 1 ≤ Y) (hd : d ∈ Nat.smoothNumbers Y) (hN : N ≤ d * Y^2) :
    (∑ p ∈ ((N + 1).primesBelow.filter (fun p => d ∣ p - 1)).filter
      (fun p => p - 1 ∈ Nat.smoothNumbers Y), w p) =
      (∑ p ∈ (N + 1).primesBelow.filter (fun p => d ∣ p - 1), w p) -
        ∑ q ∈ largePrimeBasis Y N,
          ∑ k ∈ shiftedPrimeCofactors N (d * q), w (d * q * k + 1) := by
  have hP (p : ℕ) (hp : p ∈ (N + 1).primesBelow.filter (fun p => d ∣ p - 1)) :
      2 ≤ p ∧ p - 1 < d * Y^2 := by
    have h := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
    exact ⟨h.2.two_le, by have hpN := h.1; have hp2 := h.2.two_le; omega⟩
  rw [smooth_prime_weight_eq_first_moment _ w Y hY (fun p hp => (hP p hp).1) (by
    intro p hp
    exact ⟨d, hd, (mem_filter.mp hp).2, (hP p hp).2⟩),
    largePrimeMoment_progression_eq_cofactors d Y N 1 w hd, largePrimeProducts_one]
  congr 1
  simp only [largePrimeMoment, Nat.choose_zero_right, Nat.cast_one, mul_one]

/-- The higher-order terms vanish identically in the first-moment regime. -/
lemma largePrimeMoment_progression_eq_zero_of_large_order (d Y N j : ℕ) (w : ℕ → ℝ)
    (hY : 1 ≤ Y) (hd : d ∈ Nat.smoothNumbers Y) (hN : N ≤ d * Y^j) :
    largePrimeMoment ((N + 1).primesBelow.filter (fun p => d ∣ p - 1)) w Y j = 0 := by
  apply sum_eq_zero
  intro p hp
  have hpP := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
  have hcard := largePrimeDivisors_card_lt_of_smooth_divisor Y (p - 1) d j hY
    (by have := hpP.2.two_le; omega) hd (mem_filter.mp hp).2
      (by have hpN := hpP.1; have hp2 := hpP.2.two_le; omega)
  rw [Nat.choose_eq_zero_of_lt hcard, Nat.cast_zero, mul_zero]

end Erdos821
