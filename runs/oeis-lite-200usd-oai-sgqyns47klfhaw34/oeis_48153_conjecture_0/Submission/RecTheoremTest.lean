import FormalConjectures.Util.ProblemImports

theorem self (n : Nat) : True := by
  induction n with
  | zero => trivial
  | succ n ih => exact ih

-- theorem bad (n : Nat) : False := by exact bad n
