import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

#check (inferInstance : Inhabited Prop)
#check (inferInstance : Nonempty Prop)
#check (inferInstance : Subsingleton (A216265 14 > 0))
#check (inferInstance : Subsingleton (A216265 13 > 0))
-- Expected failures:
-- #check (inferInstance : Inhabited (A216265 14 > 0))
-- #check (inferInstance : Nonempty (A216265 14 > 0))
-- #check (inferInstance : Inhabited False)
#check Classical.choice (inferInstance : Nonempty Prop)
#check default : Prop
#print axioms Classical.choice
