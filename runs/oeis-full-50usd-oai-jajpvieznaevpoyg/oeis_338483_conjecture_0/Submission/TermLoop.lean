import FormalConjectures.Util.ProblemImports

theorem badTerm : ∀ n : Nat, False
| n => badTerm n
termination_by n => n
decreasing_by
  exact Nat.lt_irrefl _

#print axioms badTerm
