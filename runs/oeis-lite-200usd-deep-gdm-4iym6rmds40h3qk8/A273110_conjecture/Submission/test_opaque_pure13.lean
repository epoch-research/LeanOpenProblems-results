import FormalConjectures.Util.ProblemImports

def my_const_def (n : Nat) (P : Prop) : Nonempty P :=
  match n with
  | 0 => @my_const_def 0 P
  | m + 1 => @my_const_def m P
termination_by n
decreasing_by
  · sorry
  · omega

theorem my_false : False := Classical.choice (my_const_def 0 False)

#print axioms my_false
