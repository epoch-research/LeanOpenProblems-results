import FormalConjectures.Util.ProblemImports
theorem recTrue (n : Nat) : True := by
  cases n with
  | zero => trivial
  | succ k => exact recTrue k
#print axioms recTrue

theorem recBad (n : Nat) : False := by
  cases n with
  | zero => exact recBad 0
  | succ k => exact recBad k
#print axioms recBad
