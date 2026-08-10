import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)
example (P : Prop) : (¬¬P → P) := by classical exact not_not.mp
#print axioms Classical.choice
#print axioms Classical.decEq
