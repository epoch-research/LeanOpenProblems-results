import Submission.Spec
open Nat

#eval (Finset.range (6 * 1 + 3)).filter (fun p =>
      p.Prime ∧
      (p - 2).Prime ∧
      (6 * 1 - p).Prime ∧
      (6 * 1 + 2 - p).Prime)
