import FormalConjectures.Util.ProblemImports

#check proof_irrel_heq
#check eq_of_heq
#check heq_of_eq

example (P Q : Prop) (hp : P) (hq : Q) : HEq hp hq := proof_irrel_heq hp hq
