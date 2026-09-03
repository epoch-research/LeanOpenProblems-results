import Submission.PrimeWinnerEnergy

/-! No exact global injective sign-reversing pairing can preserve every
prime-winner label. This is a finite-input obstruction, not a density
obstruction: a density proof may discard finitely many inputs. -/

namespace Erdos371

private lemma eq_pow_of_only_prime (n p : ℕ) (hn : n ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → q = p) :
    ∃ k : ℕ, n = p ^ k := by
  refine ⟨n.factorization p, Nat.eq_pow_of_factorization_eq_single hn ?_⟩
  ext q
  by_cases hqp : q = p
  · simp [hqp]
  · rw [Finsupp.single_eq_of_ne hqp]
    by_cases hp : q.Prime
    · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hqp (h q hp hd))
    · exact Nat.factorization_eq_zero_of_not_prime n hp

private lemma three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

/-- Among ALL positive indices, the only fall whose larger largest-prime
factor is three is the transition from three to four. -/
theorem falling_primeWinner_three_unique (n : ℕ)
    (hw : primeWinner n = 3)
    (hf : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n) : n = 3 := by
  have hnP : Nat.maxPrimeFac n = 3 := by
    simpa only [primeWinner, max_eq_left hf.le] using hw
  have hn3 : 3 ≤ n := by
    simpa only [hnP] using (Nat.maxPrimeFac_le (n := n))
  have hnext : Nat.maxPrimeFac (n+1) = 2 := by
    have htwo := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).two_le
    omega
  have hdiv2 : 2 ∣ n+1 := by simpa only [hnext] using (Nat.maxPrimeFac_dvd (n := n+1))
  have hndiv2 : ¬ 2 ∣ n := by
    intro h
    exact Nat.prime_two.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hdiv2)
  obtain ⟨a, ha⟩ := eq_pow_of_only_prime (n+1) 2 (by omega) (by
    intro q hq hqn
    have hq2 := Nat.le_maxPrimeFac (by omega : n+1 ≠ 0) hq hqn
    rw [hnext] at hq2
    have := hq.two_le
    omega)
  obtain ⟨b, hb⟩ := eq_pow_of_only_prime n 3 (by omega) (by
    intro q hq hqn
    have hq3 := Nat.le_maxPrimeFac (by omega : n ≠ 0) hq hqn
    rw [hnP] at hq3
    have hq2 := hq.two_le
    have hne : q ≠ 2 := by rintro rfl; exact hndiv2 hqn
    omega)
  have ha2 : a ≤ 2 := by
    by_contra h
    have hd : 8 ∣ 2^a := by
      simpa using Nat.pow_dvd_pow 2 (show 3 ≤ a by omega)
    have he : (3^b + 1) % 8 = 0 := by
      rw [← hb, ha]
      exact Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mod] at he
    rcases three_pow_mod_eight b with h | h <;> simp [h] at he
  have hpow : 2^a ≤ 4 := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) ha2
  omega

private lemma winner_three_rising_examples :
    primeWinner 2 = 3 ∧ primeWinner 8 = 3 ∧
      factorSign 2 = 1 ∧ factorSign 8 = 1 := by
  norm_num [primeWinner, factorSign, predicateSign,
    show Nat.maxPrimeFac 2 = 2 by decide +kernel,
    show Nat.maxPrimeFac 3 = 3 by decide +kernel,
    show Nat.maxPrimeFac 8 = 2 by decide +kernel,
    show Nat.maxPrimeFac 9 = 3 by decide +kernel]

/-- This rules out an exact pairing of ALL inputs preserving the larger
prime, even if no interval-preservation condition is imposed. It does not
rule out a pairing after density-zero exceptions have been removed. -/
theorem no_injective_primeWinner_preserving_sign_reversal :
    ¬ ∃ f : ℕ → ℕ, Function.Injective f ∧
      (∀ n : ℕ, 1 < n → primeWinner (f n) = primeWinner n) ∧
      (∀ n : ℕ, 1 < n → factorSign (f n) = -factorSign n) := by
  rintro ⟨f, hinj, hw, hs⟩
  have hex := winner_three_rising_examples
  have hfall (m : ℕ) (hsgn : factorSign m = -1) :
      Nat.maxPrimeFac (m+1) < Nat.maxPrimeFac m := by
    have hnrise : ¬ Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) := by
      intro h
      norm_num [factorSign, predicateSign, h] at hsgn
    exact lt_of_le_of_ne (not_lt.mp hnrise) (consecutive_maxPrimeFac_ne m)
  have hf2 : f 2 = 3 := falling_primeWinner_three_unique (f 2)
    ((hw 2 (by decide)).trans hex.1)
    (hfall _ (by simpa only [hex.2.2.1] using hs 2 (by decide)))
  have hf8 : f 8 = 3 := falling_primeWinner_three_unique (f 8)
    ((hw 8 (by decide)).trans hex.2.1)
    (hfall _ (by simpa only [hex.2.2.2] using hs 8 (by decide)))
  have hbad := hinj (hf2.trans hf8.symm)
  omega

#print axioms falling_primeWinner_three_unique
#print axioms no_injective_primeWinner_preserving_sign_reversal

end Erdos371
