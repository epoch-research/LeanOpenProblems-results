import FormalConjectures.Util.ProblemImports
example (k : ℕ) : (Nat.fib (5 + k*5) : ℤ) = (Nat.fib (k*5 + 5) : ℤ) := by
  rw [show 5 + k * 5 = k * 5 + 5 by ring]
example (k : ℕ) : (-(1:ℤ) * ↑(Nat.fib (5 + k * 5)) * 3 + (1:ℤ) * ↑(Nat.fib (1 + k * 5)) * 7 + (1:ℤ) * ↑(Nat.fib (k * 5)) * 4 =
    -((1:ℤ) * ↑(Nat.fib (1 + k * 5)) * 8) - (1:ℤ) * ↑(Nat.fib (k * 5)) * 5) := by
  rw [show 5 + k * 5 = k * 5 + 5 by ring]
  rw [show 1 + k * 5 = k * 5 + 1 by ring]
  simp only [Nat.fib_add_two, Nat.cast_add]
  ring
