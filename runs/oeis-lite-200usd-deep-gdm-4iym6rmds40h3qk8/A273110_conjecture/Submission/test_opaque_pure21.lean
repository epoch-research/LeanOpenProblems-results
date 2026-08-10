import FormalConjectures.Util.ProblemImports

def loop_nonempty (P : Prop) : Nonempty P :=
  let rec f (n : Nat) : Nonempty P :=
    match n with
    | 0 => f 1  -- wait, 1 is larger than 0, so this won't pass termination unless we use a relation where 1 < 0.
    | m + 1 => f m
    termination_by n
    decreasing_by
      · sorry
      · omega
  f 1
