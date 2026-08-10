import FormalConjectures.Util.ProblemImports
opaque oNat : Nat
opaque p1 (n : Nat) : False := p1 (n+1)
-- if accepted
-- theorem bad : False := p1 oNat
#print axioms p1
