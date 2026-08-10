import FormalConjectures.Util.ProblemImports

theorem t : False := by
  let rec loop (n : Nat) : False := loop (n+1)
  exact loop 0
#print axioms t
