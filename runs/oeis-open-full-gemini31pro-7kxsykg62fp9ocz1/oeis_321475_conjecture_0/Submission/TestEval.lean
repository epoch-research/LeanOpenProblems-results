import Submission.Spec
open Nat List

#eval ofDigits 10 (filter (fun (d : ℕ) => decide (d ≠ 0)) (digits 10 10))
#eval ofDigits 10 (filter (fun (d : ℕ) => decide (d ≠ 0)) (digits 10 205))
