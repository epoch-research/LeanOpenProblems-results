import FormalConjectures.Util.ProblemImports

partial def arbSort (α : Sort u) : α := arbSort α

theorem arbitraryProp (P : Prop) : P := arbSort P

def arbitraryNat : Nat := arbSort Nat

#print axioms arbSort
#print axioms arbitraryProp
#print axioms arbitraryNat
