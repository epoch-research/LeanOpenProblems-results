import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

theorem test_thm : p_th_prime 2 = 3 := by
  unfold p_th_prime
  simp

#print test_thm