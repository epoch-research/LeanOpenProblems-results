import Submission.Spec
open Nat

def check_gb (n : ℕ) : Bool :=
  if n % 2 == 0 && n > 2 then
    let primes := (List.range n).filter (fun p => p >= 2 && (List.range p).all (fun d => d < 2 || p % d != 0))
    primes.any (fun p => primes.any (fun q => p + q == n))
  else true

#eval (List.range 100).all check_gb
