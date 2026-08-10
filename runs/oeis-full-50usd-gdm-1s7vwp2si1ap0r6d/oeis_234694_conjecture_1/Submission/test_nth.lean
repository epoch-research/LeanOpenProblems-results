import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

example : p_th_prime 2 = 3 := by rfl
example : p_th_prime 3 = 5 := by rfl
example : p_th_prime 5 = 11 := by rfl
