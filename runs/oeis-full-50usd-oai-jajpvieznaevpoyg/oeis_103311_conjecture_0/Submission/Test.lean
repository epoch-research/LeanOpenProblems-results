import FormalConjectures.Util.ProblemImports

example (n : ℕ) : (3 * (Nat.fib (n+3) : ℤ) - (Nat.fib (n+1):ℤ) = (Nat.fib (n+5):ℤ)) := by
  simp only [Nat.fib_add_two, Nat.cast_add, Nat.cast_mul]
  ring

example (n : ℕ) : (3 * (Nat.fib (n+5) : ℤ) - 4*(Nat.fib (n+3):ℤ) + (Nat.fib (n+1):ℤ) = (Nat.fib (n+6):ℤ)) := by
  simp only [Nat.fib_add_two, Nat.cast_add, Nat.cast_mul]
  ring

example (n : ℕ) : (3 * (Nat.fib (n+6) : ℤ) - 4*(Nat.fib (n+5):ℤ) + 2*(Nat.fib (n+3):ℤ) = (Nat.fib (n+6):ℤ)) := by
  simp only [Nat.fib_add_two, Nat.cast_add, Nat.cast_mul]
  ring

example (n : ℕ) : ((Nat.fib (n+6):ℤ) - 2*(Nat.fib (n+5):ℤ) + (Nat.fib (n+3):ℤ) = 0) := by
  simp only [Nat.fib_add_two, Nat.cast_add, Nat.cast_mul]
  ring

example (n : ℕ) : (2*(Nat.fib (n+6):ℤ) + (Nat.fib (n+5):ℤ) = (Nat.fib (n+8):ℤ)) := by
  simp only [Nat.fib_add_two, Nat.cast_add, Nat.cast_mul]
  ring
