import FormalConjectures.Util.ProblemImports

partial def trueDecSubtype (P : Prop) : {d : Decidable P // @decide P d = true} := trueDecSubtype P

#check trueDecSubtype
#print axioms trueDecSubtype

example (P : Prop) : P := by
  let dsub := trueDecSubtype P
  letI : Decidable P := dsub.1
  exact of_decide_eq_true (by simpa using dsub.2)
