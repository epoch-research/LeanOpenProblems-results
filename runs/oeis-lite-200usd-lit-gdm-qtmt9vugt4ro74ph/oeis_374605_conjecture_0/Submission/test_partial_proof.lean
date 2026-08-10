import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

partial def proof_helper (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hn1 : (2 * p + 3) / 3 ≤ n) (hn2 : n ≤ p - 1) :
    Option (PLift ((p ^ 3 : ℕ) ∣ a n)) :=
  proof_helper p n hp hp5 hn1 hn2


