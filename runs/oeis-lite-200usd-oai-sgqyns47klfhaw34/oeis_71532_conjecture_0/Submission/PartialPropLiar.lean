import FormalConjectures.Util.ProblemImports

partial def liar (u : Unit) : Prop := ¬ liar u
#print liar
#check liar.eq_def
#reduce liar ()
#check show liar () = ¬ liar () from rfl
example : False := by
  have hEq : liar () = ¬ liar () := rfl
  have hIff : liar () ↔ ¬ liar () := iff_of_eq hEq
  exact iff_not_self (a := liar ()) hIff
#print axioms liar
#print axioms _example
