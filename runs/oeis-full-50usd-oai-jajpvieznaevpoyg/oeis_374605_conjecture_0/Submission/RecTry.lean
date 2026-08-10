import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def P0 (n : ℕ) : ℤ := -16642368 -274291056*(n:ℤ) -1964534256*(n:ℤ)^2 -- truncated

example (n : ℕ) : a n = a n := by ring_nf
-- Finite sum congruence shape?
example (n : ℕ) : (∑ k ∈ Finset.range (n+1), (0:ℤ)) = 0 := by simp
