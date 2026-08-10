import FormalConjectures.Util.ProblemImports
partial def L : Prop := ¬ L
#check L
#print L
#print axioms L
#check L.eq_1
#check unfold L
example : False := by
  -- try unfold L
  change L
  -- unfold L -- probably doesn't
  have hc := Classical.propComplete L
  rcases hc with h | h
  · exact of_eq_true h
  · exact False.elim ?_
