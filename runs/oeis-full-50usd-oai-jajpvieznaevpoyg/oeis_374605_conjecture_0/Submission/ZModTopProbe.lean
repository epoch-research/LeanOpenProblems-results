import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

example (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : ((a (p-1) : ℕ) : ZMod (p^3)) = 0 := by
  unfold a
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  -- try to see if simp knows finite field only if modulus prime, but p^3 not field
  try ring_nf
  try omega
