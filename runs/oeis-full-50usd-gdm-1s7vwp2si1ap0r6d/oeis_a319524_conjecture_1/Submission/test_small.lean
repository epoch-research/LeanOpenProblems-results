import FormalConjectures.Util.ProblemImports
open Nat

theorem no_sol_y_9 (m m' k' : ℕ)
  (h1 : 23 + m * 29 = 29 + m' * 31)
  (h2 : 29 + m' * 31 = 31 + k' * 37)
  (hm' : m' < 29) : False := by omega

theorem no_sol_y_10 (m m' k' : ℕ)
  (h1 : 29 + m * 31 = 31 + m' * 37)
  (h2 : 31 + m' * 37 = 37 + k' * 41)
  (hm' : m' < 31) : False := by omega
