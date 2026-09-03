import Submission.CarriedPrimeAverage
import Submission.LambertDoldCongruence

/-!
A fixed-modulus necessary pattern for rationality of the actual carried
series. The infinite-occurrence hypothesis in the irrationality criterion
is not established; this file does not settle the original conjecture.
-/

namespace CarriedFixedModulusCriterion

open Finset Erdos68Development CongruencePreservingCarry
  CarriedRationalPrimePattern CarriedPrimeAverage

lemma enclosing_prime_gap (n : ℕ) (hn : 6 ≤ n) :
    ∃ i : ℕ, prime i < n ∧ n ≤ prime (i+1) := by
  classical
  let S := (range (n+1)).filter (fun i => prime i < n)
  have hzero : 0 ∈ S := by
    have he : prime 0 = 5 := by simp [prime, Nat.nth_prime_two_eq_five]
    simp only [S, mem_filter, mem_range, he]
    omega
  let i := S.max' ⟨0, hzero⟩
  have hi : i ∈ S := max'_mem S _
  have hp : prime i < n := (mem_filter.mp hi).2
  refine ⟨i, hp, ?_⟩
  by_contra h
  have hb := prime_ge_index i
  have hnext : i+1 ∈ S := by
    simp only [S, mem_filter, mem_range]
    omega
  have hm : i+1 ≤ i := le_max' S (i+1) hnext
  omega

lemma rational_tail_nonprime_formula (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ)
    (hn : 2*(q.den+5) ≤ n) (hnp : ¬n.Prime) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ integerTail q n = 2*(p : ℤ)-1-n := by
  obtain ⟨i, hpn, hns⟩ := enclosing_prime_gap n (by omega)
  have hp5 := prime_ge_five i
  have hslt := prime_succ_lt_twice i
  have hden : q.den ≤ prime i-1 := by omega
  have hlt : n < prime (i+1) := by
    have hs := prime_prime (i+1)
    by_contra hh
    have he : n = prime (i+1) := by omega
    exact hnp (he ▸ hs)
  refine ⟨prime i, prime_prime i, hp5, ?_⟩
  exact (rational_between_primes q hq (prime i) (prime (i+1))
    (prime_prime i) (prime_prime (i+1)) hp5 hden
    (prime_strictMono (by omega)) hslt (prime_gap i)).1 n hpn hlt

lemma rational_tail_odd_even (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ)
    (hn : 2*(q.den+5) ≤ n) (hodd : n % 2 = 1) :
    integerTail q n % 2 = 0 := by
  have hoddZ : (n : ℤ) % 2 = 1 := by exact_mod_cast hodd
  by_cases hp : n.Prime
  · obtain ⟨i, hpn, hns⟩ := enclosing_prime_gap n (by omega)
    have hslt := prime_succ_lt_twice i
    have hnseq : n = prime (i+1) := by
      by_contra hne
      exact prime_gap i n hpn (by omega) hp
    have ht := (rational_between_primes q hq (prime i) (prime (i+1))
      (prime_prime i) (prime_prime (i+1)) (prime_ge_five i) (by omega)
      (prime_strictMono (by omega)) hslt (prime_gap i)).2
    rw [← hnseq] at ht
    rw [ht]
    norm_num [Int.sub_emod, Int.mul_emod, hoddZ]
  · obtain ⟨p, _, _, ht⟩ := rational_tail_nonprime_formula q hq n hn hp
    rw [ht]
    omega

/-- Under rationality, every sufficiently late even coefficient has a
specific residue modulo four, not merely odd parity. -/
theorem rational_even_coefficient_mod_four (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ)
    (hn : 2*(q.den+6) ≤ n) (heven : n % 2 = 0) :
    coeff n % 4 = ((n : ℤ)-1) % 4 := by
  have hnp : ¬n.Prime := by
    intro hp
    have ho := hp.eq_two_or_odd
    omega
  obtain ⟨p, hp, hp5, ht⟩ := rational_tail_nonprime_formula q hq n (by omega) hnp
  have hpo := hp.eq_two_or_odd
  have hpoZ : (p : ℤ) % 2 = 1 := by exact_mod_cast (show p % 2 = 1 by omega)
  have hmodT : integerTail q n % 4 = (1-(n : ℤ)) % 4 := by
    rw [ht]
    omega
  have hprev := rational_tail_odd_even q hq (n-1) (by omega) (by omega)
  have hnZ : (n : ℤ) % 2 = 0 := by exact_mod_cast heven
  have hprod : ((n : ℤ)*integerTail q (n-1)) % 4 = 0 := by
    obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hnZ
    obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero hprev
    apply Int.emod_eq_zero_of_dvd
    refine ⟨a*b, ?_⟩
    rw [ha, hb]
    ring
  have hs := integerTail_succ q hq (n-1) (by omega)
  rw [show n-1+1 = n by omega] at hs
  have hs' : coeff n = (n : ℤ)*integerTail q (n-1)-integerTail q n := by
    have hcast : ((n-1 : ℕ) : ℤ)+1 = n := by omega
    rw [hcast] at hs
    omega
  rw [hs', Int.sub_emod, hprod, hmodT]
  omega

/-- The Dold congruence modulo four between 2m and 4m would be enough at
arbitrarily large odd m. It is not asserted to survive the actual carry. -/
theorem irrational_of_frequent_dold_mod_four
    (hinherit : ∀ M : ℕ, ∃ m ≥ M, m % 2 = 1 ∧
      (4 : ℤ) ∣ coeff (4*m)-coeff (2*m)) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨m, hm, hodd, hdiv⟩ := hinherit (q.den+6)
  have h4 := rational_even_coefficient_mod_four q hq.symm (4*m) (by omega) (by omega)
  have h2 := rational_even_coefficient_mod_four q hq.symm (2*m) (by omega) (by omega)
  have hmZ : (m : ℤ) % 2 = 1 := by exact_mod_cast hodd
  have hdiv' := Int.emod_eq_zero_of_dvd hdiv
  push_cast at h4 h2
  omega

/-- A still simpler sufficient condition: arbitrarily late even indices
whose actual carried coefficient is even. No such infinite occurrence is
proved here. -/
theorem irrational_of_frequent_even_coefficients
    (heven : ∀ M : ℕ, ∃ n ≥ M, n % 2 = 0 ∧ coeff n % 2 = 0) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨n, hn, hn2, hc2⟩ := heven (2*(q.den+6))
  have h4 := rational_even_coefficient_mod_four q hq.symm n hn hn2
  have hnZ : (n : ℤ) % 2 = 0 := by exact_mod_cast hn2
  omega

/-- The original Lambert coefficients do satisfy the relation appearing in
the conditional criterion. This is not a statement about the carried ones. -/
lemma original_dold_mod_four (m : ℕ) (hm : 2 ≤ m) :
    Nat.ModEq 4 (lambertCoeff (4*m)) (lambertCoeff (2*m)) := by
  have h := LambertDoldCongruence.lambertCoeff_dold 2 1 m (by decide) (by omega)
  norm_num only [Nat.reduceAdd, Nat.reducePow, pow_one] at h
  have hfac : 4 ∣ (2*m).factorial := Nat.dvd_factorial (by decide) (by omega)
  have hfacmod := Nat.mod_eq_zero_of_dvd hfac
  change lambertCoeff (4*m) % 4 = (lambertCoeff (2*m)+(2*m).factorial) % 4 at h
  simpa only [Nat.ModEq, Nat.add_mod, hfacmod, Nat.add_zero, Nat.mod_mod] using h

/-- Even parity is already possible for the actual carried sequence; the
criterion requires it infinitely often, not merely at this one index. -/
lemma coefficient_six : coeff 6 = 26 := by
  have h3 : lambertPrefix 3 = 4 := by decide
  have h4 : lambertPrefix 4 = 23 := by decide
  have h5 : lambertPrefix 5 = 116 := by decide
  have h6 : lambertPrefix 6 = 807 := by decide
  have ha : lambertCoeff 6 = 111 := by decide
  norm_num [coeff, coeffRow, CongruencePreservingCarry.carry, y, scaledSumQ,
    Finset.sum_range_succ, Nat.factorial, h3, h4, h5, h6, ha]

end CarriedFixedModulusCriterion

#print axioms CarriedFixedModulusCriterion.rational_even_coefficient_mod_four
#print axioms CarriedFixedModulusCriterion.irrational_of_frequent_dold_mod_four

#print axioms CarriedFixedModulusCriterion.irrational_of_frequent_even_coefficients
#print axioms CarriedFixedModulusCriterion.original_dold_mod_four
#print axioms CarriedFixedModulusCriterion.coefficient_six
