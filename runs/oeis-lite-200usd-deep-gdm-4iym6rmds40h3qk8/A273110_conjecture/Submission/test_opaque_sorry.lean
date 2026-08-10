import Lean

opaque my_opaque : Nat := (sorry : Nat)

def my_theorem : Nat := my_opaque

#print axioms my_opaque
#print axioms my_theorem
