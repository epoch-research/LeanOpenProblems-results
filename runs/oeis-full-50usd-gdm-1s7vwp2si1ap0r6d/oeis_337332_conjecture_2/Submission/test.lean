import FormalConjectures.Util.ProblemImports

theorem g_prime_identity (n : ℕ) (q'' h' : ℤ) (v : ℤ)
    (h_q''_def : q'' = ((n : ℤ) + 3) * (h' + 4 * v) - 2 * h' - 7 * v) :
    2 * h' + 7 * v = ((n : ℤ) + 3) * (h' + 4 * v - q'') := by
  rw [h_q''_def]
  ring

