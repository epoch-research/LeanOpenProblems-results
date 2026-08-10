import FormalConjectures.Util.ProblemImports

axiom P : Prop

noncomputable instance selfFactNamed : Fact P := ⟨@Fact.out P selfFactNamed⟩

example : P := Fact.out

#print axioms selfFactNamed
#print axioms _example
