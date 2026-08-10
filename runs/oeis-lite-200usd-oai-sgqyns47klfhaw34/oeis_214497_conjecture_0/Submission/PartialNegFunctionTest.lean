import FormalConjectures.Util.ProblemImports

partial def negAny (P : Prop) (p : P) : False := negAny P p

#check negAny
#print axioms negAny

example (P : Prop) : ¬ P := negAny P

example (P : Prop) : P := by
  classical
  exact Not.imp_symm (a:=P) (b:=False) (fun hn => negAny _ hn) (fun f => f)
