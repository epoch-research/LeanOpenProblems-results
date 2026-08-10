import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

partial def oeis_374605_conjecture_0_partial (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n : ℕ) (hn1 : (2 * p + 3) / 3 ≤ n) (hn2 : n ≤ p - 1) :
    (p ^ 3 : ℕ) ∣ a n :=
  oeis_374605_conjecture_0_partial p hp hp5 n hn1 hn2

#print axioms oeis_374605_conjecture_0_partial
