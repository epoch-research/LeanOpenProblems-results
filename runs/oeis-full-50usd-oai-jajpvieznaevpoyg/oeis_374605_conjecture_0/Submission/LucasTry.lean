import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

example (p : ℕ) [Fact p.Prime] (n k : ℕ) (hn : n < p^2) (hk : k < p^2) :
    Nat.choose n k ≡ ∏ i ∈ Finset.range 2, Nat.choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] := by
  exact Choose.choose_modEq_prod_range_choose_nat hn hk
