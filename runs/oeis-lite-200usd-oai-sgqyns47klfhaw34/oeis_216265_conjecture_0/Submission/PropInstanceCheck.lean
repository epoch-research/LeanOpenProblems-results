import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

#check (inferInstance : Subsingleton (A216265 14 > 0))
-- #check (inferInstance : Nonempty (A216265 14 > 0))
-- #check Classical.choice (inferInstance : Nonempty (A216265 14 > 0))
example (P : Prop) [h : Nonempty P] : P := Classical.choice h
example (P : Prop) [Subsingleton P] : True := trivial
