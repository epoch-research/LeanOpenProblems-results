import FormalConjectures.Util.ProblemImports
open Nat

theorem no_sol_y_9 (m m' k' : ℕ)
  (h1 : 23 + m * 29 = 29 + m' * 31)
  (h2 : 29 + m' * 31 = 31 + k' * 37)
  (hm' : m' < 29) : False := by
  omega
