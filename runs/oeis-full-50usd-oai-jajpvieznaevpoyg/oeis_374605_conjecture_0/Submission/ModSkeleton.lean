import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

example (p n : ℕ) : ((p^3 : ℕ) ∣ a n) ↔ ((a n : ZMod (p^3)) = 0) := by
  rw [ZMod.natCast_eq_zero_iff]

example (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) : (p ^ 3 : ℕ) ∣ a (p-1) := by
  rw [← ZMod.natCast_eq_zero_iff]
  dsimp [a]
  -- try simplification only
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  sorry
