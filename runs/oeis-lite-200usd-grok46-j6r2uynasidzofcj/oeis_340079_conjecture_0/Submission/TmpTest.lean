import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

set_option maxHeartbeats 8000000

lemma prime_3 : Nat.Prime 3 := by norm_num
lemma prime_37 : Nat.Prime 37 := by norm_num
lemma prime_43 : Nat.Prime 43 := by norm_num
lemma prime_42307 : Nat.Prime 42307 := by norm_num
lemma prime_116341 : Nat.Prime 116341 := by norm_num

lemma n_pf : (3 * 37 * 43 * 42307 * 116341).primeFactors =
    {3, 37, 43, 42307, 116341} := by
  rw [primeFactors_mul (by norm_num : 3 * 37 * 43 * 42307 ≠ 0) (by norm_num : 116341 ≠ 0)]
  rw [primeFactors_mul (by norm_num : 3 * 37 * 43 ≠ 0) (by norm_num : 42307 ≠ 0)]
  rw [primeFactors_mul (by norm_num : 3 * 37 ≠ 0) (by norm_num : 43 ≠ 0)]
  rw [primeFactors_mul (by norm_num : 3 ≠ 0) (by norm_num : 37 ≠ 0)]
  rw [prime_3.primeFactors, prime_37.primeFactors, prime_43.primeFactors,
    prime_42307.primeFactors, prime_116341.primeFactors]
  decide

#print axioms n_pf
