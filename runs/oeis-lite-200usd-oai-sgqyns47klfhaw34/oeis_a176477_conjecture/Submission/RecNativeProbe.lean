import FormalConjectures.Util.ProblemImports

def pow2Prop (n : Nat) := ∃ m : Nat, m ≥ 1 ∧ n = 2^m
example : (n : Nat) -> n = n := by
  intro n
  induction n with
  | zero => native_decide
  | succ k ih => native_decide

example : (n : Nat) -> (pow2Prop n ∨ ¬ pow2Prop n) := by
  intro n
  induction n with
  | zero => native_decide
  | succ k ih => native_decide
