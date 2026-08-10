import Submission.Spec

open Nat Set

#check (oeis_53000_conjecture_1 : ∀ (n : ℕ) (hn : n > 0), (sInf {p | Nat.Prime p ∧ p > n ^ 2} - n ^ 2) ≤ 1 + Nat.totient n)
#synth InfSet ℕ
