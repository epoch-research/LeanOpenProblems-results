import FormalConjectures.Util.ProblemImports

open Polynomial Finset Nat

noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Polynomial ℤ :=
    (Ico 1 (n + 1)).prod fun k : ℕ =>
      (1 - X ^ k) ^ (n * k)
  P_n.coeff n

theorem oeis_281267_conjecture_0 (p : ℕ) (n k : ℕ) :
  Nat.Prime p → 3 ≤ p → 1 ≤ n → 1 ≤ k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p ^ (2 * k) : ℕ) : ℤ)] := answer(sorry)

#print axioms oeis_281267_conjecture_0

