import FormalConjectures.Util.ProblemImports

def aa (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

example : (5^3 : ℕ) ∣ aa 4 := by native_decide
example (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : False := by
  -- try aesop/omega
  aesop
