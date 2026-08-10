import FormalConjectures.Util.ProblemImports

opaque oFalse : False
opaque oSubNat : Subsingleton Nat
opaque oInhFalse : Inhabited False
noncomputable opaque oDec (P : Prop) : Decidable P

#print axioms oFalse
#print axioms oSubNat
#print axioms oInhFalse
#print axioms oDec
