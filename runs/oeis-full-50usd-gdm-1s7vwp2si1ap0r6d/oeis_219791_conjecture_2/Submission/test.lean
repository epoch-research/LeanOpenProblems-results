import FormalConjectures.Util.ProblemImports

open Nat Finset

theorem oeis_219791_conjecture_2_test :
  ∀ (k : ℕ), 0 < k →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2^k) + 1) :=
  answer(sorry)
#print axioms oeis_219791_conjecture_2_test
#check oeis_219791_conjecture_2_test
