import FormalConjectures.Util.ProblemImports
#eval Fintype.card Prop
#check Fintype.card_prop
#check Fintype.card_bool
example : Fintype.card Prop = 2 := by native_decide
example (P : Prop) : P := by
  have hcard : Fintype.card Prop = 1 := by
    try simp
    try native_decide
  have heq : P = True := by
    -- maybe from card=1?
    sorry
  exact Eq.mpr heq.symm True.intro
