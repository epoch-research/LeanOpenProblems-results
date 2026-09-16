import Submission.Spec
open Nat

#eval (List.range 100).find? (fun n => n % 2 == 0 && n > 2 && (List.range n).all (fun p =>
  !(p >= 2 && (List.range p).all (fun d => d < 2 || p % d != 0) &&
    (n - p) >= 2 && (List.range (n - p)).all (fun d => d < 2 || (n - p) % d != 0))))
