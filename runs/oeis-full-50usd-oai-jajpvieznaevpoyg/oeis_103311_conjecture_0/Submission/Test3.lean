import FormalConjectures.Util.ProblemImports
example (k : ℕ) : (3 * (Nat.fib (5*k+3):ℤ) - (Nat.fib (5*k+1):ℤ) = (Nat.fib (5*k+1+4):ℤ)) := by
  ring_nf
  rw [show 1 + k * 5 = k * 5 + 1 by ring,
      show 3 + k * 5 = k * 5 + 3 by ring,
      show 5 + k * 5 = k * 5 + 5 by ring]
  simp only [Nat.fib_add_two, Nat.cast_add]
  ring
