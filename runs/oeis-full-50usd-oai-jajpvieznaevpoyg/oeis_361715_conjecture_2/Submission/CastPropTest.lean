import FormalConjectures.Util.ProblemImports

example (P Q : Prop) (h : P = Q) (p : P) : Q := by cases h; exact p

example : False := by
  have h : False = True := by
    -- impossible
    exact propext (Iff.intro (fun h => False.elim h) (fun _ => by trivial))
  have t : True := True.intro
  exact (show False from (by cases h; exact t))
