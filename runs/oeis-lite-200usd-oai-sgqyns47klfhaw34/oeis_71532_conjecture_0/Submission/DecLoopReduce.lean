import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P
#reduce decLoop False
