import FormalConjectures.Util.ProblemImports

def my_const_def (n : Nat) (P : Prop) : Nonempty P :=
  match n with
  | 0 => @my_const_def 0 P
  | m + 1 => @my_const_def m P
termination_by n
decreasing_by
  · sorry
  · omega

-- Since `my_const_def 1 P` reduces to `my_const_def 0 P`, and `my_const_def 0 P` is the one with `sorryAx` in its termination,
-- any use of `my_const_def` might transitively depend on `sorryAx` if the definition is unfolded or if the whole mutual block depends on it.
-- Indeed, in Lean, if a definition uses `sorry`, the whole definition (and anything referencing it) is flagged with `sorryAx`.
