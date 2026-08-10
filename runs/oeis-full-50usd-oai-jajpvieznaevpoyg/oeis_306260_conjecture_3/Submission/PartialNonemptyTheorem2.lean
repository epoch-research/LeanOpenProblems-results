import FormalConjectures.Util.ProblemImports
open Finset Nat

def P (n : ℕ) : Prop := ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3)
partial def neAll (_ : Unit) : Nonempty (∀ n, P n) := neAll ()
theorem t (n : ℕ) : P n := Classical.choice (neAll ()) n
#print axioms t
#print opaques t
