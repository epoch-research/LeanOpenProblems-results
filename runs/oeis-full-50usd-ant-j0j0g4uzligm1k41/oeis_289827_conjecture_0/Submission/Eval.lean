import Mathlib
open scoped Nat.Prime
def A (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n
def bad : List ℕ := (List.range 1201).filterMap (fun n =>
  if 1 < n ∧ A n ≠ 1 ∧ A n ≠ 2 ∧ A n ≠ 4 ∧ A n ≠ 10 then some n else none)
#eval bad
