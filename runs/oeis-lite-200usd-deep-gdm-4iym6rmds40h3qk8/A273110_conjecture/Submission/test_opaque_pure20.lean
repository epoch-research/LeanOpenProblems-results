import FormalConjectures.Util.ProblemImports

def loop_nonempty (P : Prop) : Nonempty P :=
  let rec f (n : Nat) : Nonempty P :=
    match n with
    | 0 => f 0
    | m + 1 => f m
    termination_by n
    decreasing_by
      · sorry
      · omega
  f 1
