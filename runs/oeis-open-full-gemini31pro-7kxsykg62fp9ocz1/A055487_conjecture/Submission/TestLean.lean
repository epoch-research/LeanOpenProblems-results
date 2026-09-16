import Submission.Spec
open Set Nat

def check_n4 : Bool :=
  let N := 24
  let cands := { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }
  True

