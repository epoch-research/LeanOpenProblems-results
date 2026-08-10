import FormalConjectures.Util.ProblemImports
example : (n : Nat) -> n = n := by
  intro n
  induction n with
  | zero => native_decide
  | succ k ih => native_decide +revert
