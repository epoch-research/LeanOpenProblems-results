import Submission.ParityDiscrepancyInterval

/-! Parity discrepancies of reduced residues cannot be bounded by a constant
multiple of the number of odd sieving primes on all long intervals.
The lengths here are complete-period multiples, NOT exact quadratic lengths. -/
namespace Erdos970.ParityDiscrepancy
open Finset

lemma energy_product_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    (4 / 3 : ℚ) ^ P.card ≤ ∏ p ∈ P, (2 - 2 / (p : ℚ)) := by
  rw [← prod_const]
  apply prod_le_prod (fun p hp => by norm_num)
  intro p hp
  have hp2 := (hP p hp).1.two_le
  have hpodd := (hP p hp).2
  have hp3 : 3 ≤ p := by obtain ⟨t, ht⟩ := hpodd; omega
  have hp3Q : (3 : ℚ) ≤ p := by exact_mod_cast hp3
  have hp0 : (0 : ℚ) < p := by linarith
  have hdiv : 2 / (p : ℚ) ≤ 2 / 3 := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  linarith

/-- Large second moment forces an actual interval parity imbalance. -/
theorem exists_large_alternatingCount (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (B : ℚ) (hB : 0 ≤ B)
    (hbig : B ^ 2 < (4 / 3 : ℚ) ^ P.card) (t : ℕ) (ht : Odd t) :
    ∃ a < primeProduct P, B < |alternatingCount P (a + 1) (primeProduct P * t)| := by
  have hN : (0 : ℚ) < primeProduct P := by
    exact_mod_cast primeProduct_pos P (fun p hp => (hP p hp).1.pos)
  have he := alternatingCount_energy P hP t ht
  have hprod := energy_product_lower P hP
  have hs : (∑ a ∈ range (primeProduct P), B ^ 2) <
      ∑ a ∈ range (primeProduct P), alternatingCount P (a + 1) (primeProduct P * t) ^ 2 := by
    rw [he]
    simp only [sum_const, card_range, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left (hbig.trans_le hprod) hN
  obtain ⟨a, ha, hlarge⟩ := exists_lt_of_sum_lt hs
  refine ⟨a, mem_range.mp ha, ?_⟩
  have hab := abs_nonneg (alternatingCount P (a + 1) (primeProduct P * t))
  have heq := sq_abs (alternatingCount P (a + 1) (primeProduct P * t))
  nlinarith

lemma exists_odd_prime_set (k : ℕ) :
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧ Odd p := by
  induction k with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨P, hcard, hP⟩ := ih
    obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (P.sup id + 3)
    have hpP : p ∉ P := by
      intro hpP
      have hh : p ≤ P.sup id := by simpa only [id_eq] using le_sup (f := id) hpP
      omega
    refine ⟨insert p P, by simp [hpP, hcard], ?_⟩
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact ⟨hp, hp.odd_of_ne_two (by omega)⟩
    · exact hP q hq

lemma cubic_growth (A t : ℕ) (ht : 0 < t) (hT : 243 * (A : ℚ) ^ 2 < t) :
    ((A : ℚ) * (3 * t : ℕ)) ^ 2 < (4 / 3 : ℚ) ^ (3 * t) := by
  have htQ : (0 : ℚ) < t := by exact_mod_cast ht
  have hmul := mul_lt_mul_of_pos_right hT (sq_pos_of_pos htQ)
  have hber : 1 + (t : ℚ) / 3 ≤ (4 / 3 : ℚ) ^ t := by
    simpa only [show (1 : ℚ) + 1 / 3 = 4 / 3 by norm_num, mul_one_div] using
      one_add_mul_le_pow (by norm_num : (-2 : ℚ) ≤ 1 / 3) t
  have hcube := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 1 + (t : ℚ) / 3) hber 3
  have heq : (4 / 3 : ℚ) ^ (3 * t) = ((4 / 3 : ℚ) ^ t) ^ 3 := by
    rw [Nat.mul_comm 3 t, pow_mul]
  rw [heq]
  push_cast
  nlinarith [hcube]

/-- An elementary cubic Bernoulli bound suffices; no asymptotic theorem is used. -/
lemma exists_exponential_dominates_linear (A K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ ((A : ℚ) * k) ^ 2 < (4 / 3 : ℚ) ^ k := by
  let t : ℕ := 1000 * (A + K + 1) ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : K ≤ (A + K + 1) ^ 2 :=
    (show K ≤ A + K + 1 by omega).trans (Nat.le_self_pow (by decide) _)
  have hKt : K ≤ 3 * t := by
    dsimp [t]
    omega
  refine ⟨3 * t, hKt, by omega, cubic_growth A t ht ?_⟩
  dsimp [t]
  push_cast
  have hA := Nat.cast_nonneg (α := ℚ) A
  have hK := Nat.cast_nonneg (α := ℚ) K
  nlinarith [sq_nonneg ((A : ℚ) + K)]

/-- No constant multiple of the prime count bounds parity imbalance on all
intervals, even after imposing an arbitrary quadratic lower length and discarding
any finite initial range of prime counts. The constructed intervals can be very
long compared with the quadratic scale. -/
theorem unbounded_parity_discrepancy (A C M K : ℕ) :
    ∃ (P : Finset ℕ) (a m : ℕ),
      (∀ p ∈ P, p.Prime ∧ Odd p) ∧ K ≤ P.card ∧ 0 < P.card ∧
      M ≤ m ∧ C * P.card ^ 2 ≤ m ∧
      (A : ℚ) * P.card < |alternatingCount P a m| := by
  obtain ⟨k, hK, hk, hpow⟩ := exists_exponential_dominates_linear A K
  obtain ⟨P, hcard, hP⟩ := exists_odd_prime_set k
  let t := 2 * (M + C * k ^ 2) + 1
  have ht : Odd t := ⟨M + C * k ^ 2, rfl⟩
  have hN := primeProduct_pos P (fun p hp => (hP p hp).1.pos)
  have hbig : ((A : ℚ) * P.card) ^ 2 < (4 / 3 : ℚ) ^ P.card := by rwa [hcard]
  obtain ⟨a, ha, hdisc⟩ := exists_large_alternatingCount P hP ((A : ℚ) * P.card)
    (by positivity) hbig t ht
  refine ⟨P, a + 1, primeProduct P * t, hP, by omega, by omega, ?_, ?_, hdisc⟩
  · have hle := Nat.le_mul_of_pos_left t hN
    exact (show M ≤ t by dsimp [t]; omega).trans hle
  · have hle := Nat.le_mul_of_pos_left t hN
    rw [hcard]
    exact (show C * k ^ 2 ≤ t by dsimp [t]; omega).trans hle

#print axioms exists_large_alternatingCount
#print axioms unbounded_parity_discrepancy
end Erdos970.ParityDiscrepancy
