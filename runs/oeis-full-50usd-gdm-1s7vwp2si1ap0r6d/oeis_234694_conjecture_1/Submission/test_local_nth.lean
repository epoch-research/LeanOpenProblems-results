import FormalConjectures.Util.ProblemImports

open Nat

-- Redefine Nat.nth locally!
local def Nat.nth (p : ℕ → Prop) (n : ℕ) : ℕ := n + 2

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

#print p_th_prime
