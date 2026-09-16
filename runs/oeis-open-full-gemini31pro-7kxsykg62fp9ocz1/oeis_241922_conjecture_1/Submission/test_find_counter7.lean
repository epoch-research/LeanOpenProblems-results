import Submission.Spec
open Nat

def g (n : ℕ) : Prop := Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

#check g
