import Submission.ParityDiscrepancyInterval

/-! Exact counting identities for sieving by the odd primes up to a cutoff.
Below the square of the cutoff, odd survivors are one and the larger primes. -/
namespace Erdos970.ParityDiscrepancy
open Finset

def oddPrimes (y : ℕ) : Finset ℕ := (range (y + 1)).filter (fun p => p.Prime ∧ Odd p)

lemma mem_oddPrimes (p y : ℕ) : p ∈ oddPrimes y ↔ p ≤ y ∧ p.Prime ∧ Odd p := by
  simp only [oddPrimes, mem_filter, mem_range, Nat.lt_succ_iff]

lemma oddPrimes_properties (y : ℕ) : ∀ p ∈ oddPrimes y, p.Prime ∧ Odd p :=
  fun p hp => (mem_oddPrimes p y).mp hp |>.2

lemma oddPrime_ne_two {p : ℕ} (hp : Odd p) : p ≠ 2 := by
  obtain ⟨t, ht⟩ := hp
  omega

lemma oddPrimes_card_le (s : ℕ) : (oddPrimes (2 * s)).card ≤ s := by
  have hmap (p : ℕ) (hp : p ∈ oddPrimes (2 * s)) : p / 2 ∈ range s := by
    obtain ⟨hle, hprime, hodd⟩ := (mem_oddPrimes p _).mp hp
    have hmod := Nat.odd_iff.mp hodd
    exact mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun p : ℕ => p / 2) (↑(oddPrimes (2 * s)) : Set ℕ) := by
    intro p hp q hq hpq
    change p / 2 = q / 2 at hpq
    have hpm := Nat.odd_iff.mp ((mem_oddPrimes p _).mp hp).2.2
    have hqm := Nat.odd_iff.mp ((mem_oddPrimes q _).mp hq).2.2
    omega
  have h := card_le_card_of_injOn (s := oddPrimes (2 * s)) (t := range s)
    (fun p : ℕ => p / 2) hmap hinj
  simpa only [card_range] using h

lemma survivorIndicator_double (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (n : ℕ) :
    survivorIndicator P (2 * n) = survivorIndicator P n := by
  have heq : (∀ p ∈ P, ¬p ∣ 2 * n) ↔ ∀ p ∈ P, ¬p ∣ n := by
    apply forall₂_congr
    intro p hp
    have hp2 : ¬p ∣ 2 := by
      intro h
      have he := (Nat.dvd_prime Nat.prime_two).mp h
      rcases he with h | h
      · exact (hP p hp).1.ne_one h
      · exact oddPrime_ne_two (hP p hp).2 h
    simp only [(hP p hp).1.dvd_mul, hp2, false_or]
  simp only [survivorIndicator, heq]

def totalSurvivorCount (P : Finset ℕ) (m : ℕ) : ℚ :=
  ∑ j ∈ range m, survivorIndicator P (j + 1)

def oddSurvivorCount (P : Finset ℕ) (m : ℕ) : ℚ :=
  ∑ j ∈ range m, if Odd (j + 1) then survivorIndicator P (j + 1) else 0

lemma alternating_eq_two_odd_sub_total (P : Finset ℕ) (m : ℕ) :
    alternatingCount P 1 m = 2 * oddSurvivorCount P m - totalSurvivorCount P m := by
  simp only [alternatingCount, oddSurvivorCount, totalSurvivorCount, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have hpar : Odd (j + 1) ↔ Even j := by rw [Nat.odd_iff, Nat.even_iff]; omega
  simp only [neg_one_pow_eq_ite, hpar, Nat.add_comm 1 j]
  split_ifs <;> ring

lemma sum_pairs (f : ℕ → ℚ) (m : ℕ) :
    (∑ j ∈ range (2 * m), f j) = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  rw [sum_blocks]
  apply sum_congr rfl
  intro j hj
  norm_num [sum_range_succ, Nat.add_comm]

lemma oddSurvivorCount_double (P : Finset ℕ) (m : ℕ) :
    oddSurvivorCount P (2 * m) = ∑ j ∈ range m, survivorIndicator P (2 * j + 1) := by
  rw [oddSurvivorCount, sum_pairs]
  apply sum_congr rfl
  intro j hj
  have ho : Odd (2 * j + 1) := ⟨j, rfl⟩
  have he : ¬Odd (2 * j + 1 + 1) := by rw [Nat.odd_iff]; omega
  simp only [ho, he, if_true, if_false, add_zero]

lemma alternating_double (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (m : ℕ) :
    alternatingCount P 1 (2 * m) = oddSurvivorCount P (2 * m) - totalSurvivorCount P m := by
  rw [alternatingCount, sum_pairs, oddSurvivorCount_double, totalSurvivorCount, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have he : (-1 : ℚ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  have ho : (-1 : ℚ) ^ (2 * j + 1) = -1 := by rw [pow_succ, he]; norm_num
  rw [he, ho, show 1 + (2 * j + 1) = 2 * (j + 1) by omega,
    survivorIndicator_double P hP]
  simp only [Nat.add_comm 1 (2 * j)]
  ring

lemma alternating_doubling_difference (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (m : ℕ) :
    alternatingCount P 1 (2 * m) - alternatingCount P 1 m =
      oddSurvivorCount P (2 * m) - 2 * oddSurvivorCount P m := by
  rw [alternating_double P hP, alternating_eq_two_odd_sub_total]
  ring

lemma odd_survivor_iff (y n : ℕ) (hy : 2 ≤ y) (hn : 0 < n) (hny : n ≤ y ^ 2) :
    (Odd n ∧ ∀ p ∈ oddPrimes y, ¬p ∣ n) ↔ n = 1 ∨ (n.Prime ∧ y < n) := by
  constructor
  · rintro ⟨hodd, hsurv⟩
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · right
      have hnp : n.Prime := by
        by_contra hnot
        have hp := Nat.minFac_prime hn1
        have hpdiv := Nat.minFac_dvd n
        have hp2 : n.minFac ≠ 2 := by
          intro heq
          rw [heq] at hpdiv
          have hmod := Nat.odd_iff.mp hodd
          have hz := Nat.mod_eq_zero_of_dvd hpdiv
          omega
        have hpsq := Nat.minFac_sq_le_self hn hnot
        have hple : n.minFac ≤ y := by nlinarith
        exact hsurv n.minFac ((mem_oddPrimes _ _).mpr ⟨hple, hp, hp.odd_of_ne_two hp2⟩) hpdiv
      refine ⟨hnp, ?_⟩
      by_contra h
      exact hsurv n ((mem_oddPrimes _ _).mpr ⟨by omega, hnp, hodd⟩) (dvd_refl n)
  · rintro (rfl | ⟨hp, hyn⟩)
    · refine ⟨by decide, ?_⟩
      intro p hpm hd
      exact ((mem_oddPrimes p y).mp hpm).2.1.not_dvd_one hd
    · refine ⟨hp.odd_of_ne_two (by omega), ?_⟩
      intro p hpm hd
      obtain ⟨hpy, hpp, hpo⟩ := (mem_oddPrimes p y).mp hpm
      have heq := (Nat.dvd_prime hp).mp hd
      rcases heq with heq | heq
      · exact hpp.ne_one heq
      · omega

lemma sum_prime_indicator (m : ℕ) :
    (∑ j ∈ range m, if (j + 1).Prime then (1 : ℚ) else 0) = m.primeCounting := by
  rw [sum_boole]
  congr 1
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ']
  simp only [Nat.not_prime_zero, if_false, add_zero, Nat.count_eq_card_filter_range]

lemma sum_small_prime_indicator (y m : ℕ) (hym : y ≤ m) :
    (∑ j ∈ range m, if (j + 1).Prime ∧ j + 1 ≤ y then (1 : ℚ) else 0) = y.primeCounting := by
  have heq : (∑ j ∈ range m, if (j + 1).Prime ∧ j + 1 ≤ y then (1 : ℚ) else 0) =
      ∑ j ∈ range y, if (j + 1).Prime ∧ j + 1 ≤ y then (1 : ℚ) else 0 := by
    symm
    apply sum_subset (range_mono hym)
    intro j hj hjy
    have hjge : y ≤ j := by simpa only [mem_range, not_lt] using hjy
    simp [show ¬j + 1 ≤ y by omega]
  rw [heq, ← sum_prime_indicator y]
  apply sum_congr rfl
  intro j hj
  simp only [show j + 1 ≤ y from mem_range.mp hj, and_true]

/-- Exact count of odd survivors below the square of the cutoff. -/
theorem oddSurvivorCount_eq (y m : ℕ) (hy : 2 ≤ y) (hym : y ≤ m) (hmy : m ≤ y ^ 2) :
    oddSurvivorCount (oddPrimes y) m = (m.primeCounting : ℚ) - y.primeCounting + 1 := by
  have hterm (j : ℕ) (hj : j ∈ range m) :
      (if Odd (j + 1) then survivorIndicator (oddPrimes y) (j + 1) else 0) =
        (if j = 0 then (1 : ℚ) else 0) + (if (j + 1).Prime then 1 else 0) -
          (if (j + 1).Prime ∧ j + 1 ≤ y then 1 else 0) := by
    have heq := odd_survivor_iff y (j + 1) hy (by omega) (by have := mem_range.mp hj; omega)
    have hite : (if Odd (j + 1) then survivorIndicator (oddPrimes y) (j + 1) else 0) =
        if Odd (j + 1) ∧ ∀ p ∈ oddPrimes y, ¬p ∣ j + 1 then (1 : ℚ) else 0 := by
      simp only [survivorIndicator, ite_and]
    rw [hite]
    simp only [heq, Nat.add_eq_right]
    by_cases hj0 : j = 0
    · subst j; norm_num
    · by_cases hjp : (j + 1).Prime <;> by_cases hjy : j + 1 ≤ y <;>
        simp [hj0, hjp, hjy, show (y < j + 1) ↔ ¬j + 1 ≤ y by omega]
  rw [oddSurvivorCount, sum_congr rfl hterm, sum_sub_distrib, sum_add_distrib,
    sum_prime_indicator, sum_small_prime_indicator y m hym]
  have hm : 0 < m := by omega
  simp only [sum_ite_eq', mem_range, hm, if_true]
  ring

#print axioms oddSurvivorCount_eq
#print axioms alternating_doubling_difference
end Erdos970.ParityDiscrepancy
