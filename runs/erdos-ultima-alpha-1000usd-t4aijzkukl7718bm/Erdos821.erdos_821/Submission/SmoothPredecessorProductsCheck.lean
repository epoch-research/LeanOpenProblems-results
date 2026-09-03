import Submission.SmoothPredecessorProducts
/-! Exact-type and axiom checks for the finite product construction. -/

open Erdos821.PredecessorProducts

example (E : Finset (ℕ × ℕ)) (hE : ∀ ab ∈ E, 0 < ab.1 ∧ 0 < ab.2) :
    E.card ≤ ∑ n ∈ productImage E, n.divisors.card := card_le_sum_divisors E hE

example (E : Finset (ℕ × ℕ)) (D : ℕ)
    (hE : ∀ ab ∈ E, 0 < ab.1 ∧ 0 < ab.2)
    (hD : ∀ n ∈ productImage (primePairs E), n.divisors.card ≤ D) :
    (primePairs E).card ≤ D * (primeImage E).card :=
  primePairs_card_le_mul_primeImage_card E D hE hD

example {a b y Q r : ℕ}
    (ha : a ∈ Nat.smoothNumbers y) (hb : b ∈ Nat.smoothNumbers y)
    (hQa : Q ≤ a) (hQb : Q ≤ b) (hy : y ^ r ≤ Q)
    (hp : (a * b + 1).Prime) :
    a * b + 1 ∈ Erdos821.rationalSmoothShiftedPrimes (2 * r) 1 :=
  prime_product_mem_rationalSmooth ha hb hQa hQb hy hp

example : ∃ A : Finset ℕ, A.card = 2 ∧
    (∀ a ∈ A, a ∈ Nat.smoothNumbers 4 ∧ (a + 1).Prime) ∧
    primePairs (A ×ˢ A) = ∅ := finite_pool_counterexample

#print axioms product_fiber_card_le
#print axioms card_le_sum_divisors
#print axioms card_le_mul_productImage_card
#print axioms primeImage_card
#print axioms primePairs_card_le_mul_primeImage_card
#print axioms product_root_smooth
#print axioms prime_product_mem_rationalSmooth
#print axioms primeImage_smooth
#print axioms not_prime_product_of_mod_five
#print axioms finite_pool_counterexample
