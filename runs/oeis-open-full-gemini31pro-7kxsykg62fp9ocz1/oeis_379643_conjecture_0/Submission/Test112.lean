import Submission.Spec
open Nat Finset

lemma sum_mod_8 (p_n : ℕ) :
  let count (b : ℕ) := ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card
  (count 3 : ℤ) - (count 7 : ℤ) - ((count 5 : ℤ) - (count 1 : ℤ)) = 
  (count 3 : ℤ) + (count 1 : ℤ) - ((count 7 : ℤ) + (count 5 : ℤ)) := by
  omega

lemma diff_a_b (n : ℕ) : a n - b n = 
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
  let count_primes_mod_b (b : ℕ) : ℕ := ((Finset.range (p_n + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = b)).card
  (count_primes_mod_b 3 : ℤ) + (count_primes_mod_b 1 : ℤ) - ((count_primes_mod_b 7 : ℤ) + (count_primes_mod_b 5 : ℤ)) := by
  sorry
