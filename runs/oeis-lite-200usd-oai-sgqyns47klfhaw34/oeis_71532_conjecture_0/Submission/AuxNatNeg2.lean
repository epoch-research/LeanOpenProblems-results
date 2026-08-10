import FormalConjectures.Util.ProblemImports
axiom P : Prop

def aux : (n : Nat) → n ≠ 0 → P → False
| 0, h, hp => False.elim (h rfl)
| n+1, h, hp => aux n (by omega) hp
#print axioms aux
-- cannot start with nonzero? yes use 1
example : ¬ P := aux 1 (by omega)
