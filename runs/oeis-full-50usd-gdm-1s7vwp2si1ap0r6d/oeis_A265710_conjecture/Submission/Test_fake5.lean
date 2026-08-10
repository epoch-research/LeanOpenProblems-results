import FormalConjectures.Util.ProblemImports

partial def fake_nonempty (P : Prop) : Nonempty (PLift P) :=
  fake_nonempty P

#print axioms fake_nonempty
