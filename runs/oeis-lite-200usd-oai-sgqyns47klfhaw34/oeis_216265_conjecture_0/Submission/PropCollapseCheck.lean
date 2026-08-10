import FormalConjectures.Util.ProblemImports
#check (inferInstance : Subsingleton Prop)
example (P : Prop) : P := by
  fail_if_success exact cast (Subsingleton.elim True P) True.intro
  sorry
