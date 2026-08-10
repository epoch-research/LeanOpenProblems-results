import FormalConjectures.Util.ProblemImports

def my_const_def (n : Nat) : Nonempty False :=
  if h : n > 0 then
    my_const_def (n - 1)
  else
    my_const_def 0
termination_by n
decreasing_by
  · omega
  · sorry
