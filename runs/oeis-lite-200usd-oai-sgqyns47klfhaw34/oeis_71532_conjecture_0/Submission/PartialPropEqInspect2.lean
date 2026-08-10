import FormalConjectures.Util.ProblemImports
partial def L (_ : Unit) : Prop := ¬ L ()
#check L
#print L
#print axioms L
#check L.eq_1
example : False := by
  have hc := Classical.propComplete (L ())
  rcases hc with h | h
  · exact of_eq_true h
  · have hn : ¬ L () := of_eq_false h
    -- if equation L=not L unavailable, no
    exact False.elim ?_
