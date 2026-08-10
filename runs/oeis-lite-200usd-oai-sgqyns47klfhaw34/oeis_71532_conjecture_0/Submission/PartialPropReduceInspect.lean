import FormalConjectures.Util.ProblemImports

partial def liar (_ : Unit) : Prop := ¬ liar ()
#print liar
#reduce liar ()
#check liar.eq_def
example : liar () = ¬ liar () := by rfl
