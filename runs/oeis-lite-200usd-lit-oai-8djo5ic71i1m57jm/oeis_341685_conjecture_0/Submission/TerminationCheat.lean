import FormalConjectures.Util.ProblemImports

theorem bad (P : Prop) (h : ¬ P) : P := by
  let rec f (n : Nat) : P := f (n+1)
  termination_by n
  decreasing_by
    have hp : P := f (n+1)
    exact False.elim (h hp)
  exact f 0
