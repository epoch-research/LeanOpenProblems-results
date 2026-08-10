import FormalConjectures.Util.ProblemImports
import Submission.TestSpeedFinal

open Nat

def check_one (primes : List Nat) (L : Nat) : Bool :=
  if L % 6 == 3 ∨ L % 10 == 0 ∨ L % 6 == 0 then true
  else
    let k := get_witness_final L
    if k == 0 then false
    else if k > (L - 1) / 2 then false
    else is_square_fast (totient_fast primes k * totient_fast primes (L - k))

def find_first_failed (primes : List Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, L =>
    if ¬ (check_one primes L) then
      some L
    else
      find_first_failed primes fuel (L + 1)

#eval find_first_failed primes_1414 20000 9
