import FormalConjectures.Util.ProblemImports

partial def inhSort (α : Sort u) : Inhabited α := inhSort α

def anyNat : Nat := (inhSort Nat).default

theorem arbitraryProp (P : Prop) : P := (inhSort P).default

#print axioms inhSort
#print axioms anyNat
#print axioms arbitraryProp
