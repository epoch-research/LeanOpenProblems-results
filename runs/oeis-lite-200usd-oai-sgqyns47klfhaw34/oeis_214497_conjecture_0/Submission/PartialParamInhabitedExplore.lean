import FormalConjectures.Util.ProblemImports

partial def arbitraryType (α : Type) : α := arbitraryType α
partial def arbitrarySort (α : Sort u) : α := arbitrarySort α
partial def arbitraryPropParam (P : Prop) : P := arbitraryPropParam P
partial def arbitraryTypeWithInh (α : Type) [Inhabited α] : α := arbitraryTypeWithInh α

#print axioms arbitraryType
#print axioms arbitrarySort
#print axioms arbitraryPropParam
#print axioms arbitraryTypeWithInh

example : False := arbitraryPropParam False
