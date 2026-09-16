import Mathlib
open Nat

#eval (List.range 1000).find? (fun n => n % 2 == 0 && n > 2 && !(
  let primes := (List.range n).filter (fun p =>
    p >= 2 && (List.range p).all (fun d => d < 2 || p % d != 0))
  primes.any (fun p => primes.any (fun q => p + q == n))
))
