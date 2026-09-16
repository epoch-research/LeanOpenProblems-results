import Mathlib
open Nat
def my_count_primes : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n+1).Prime then my_count_primes n + 1 else my_count_primes n
#eval my_count_primes 1000000
