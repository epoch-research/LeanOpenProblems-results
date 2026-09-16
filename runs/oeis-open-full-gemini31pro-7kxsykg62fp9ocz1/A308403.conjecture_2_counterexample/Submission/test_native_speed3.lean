import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false else Nat.minFac n == n

def nthPrimeFuel (fuel : ℕ) (n : ℕ) (i : ℕ) (c : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if c > n then i - 1
    else
      let c' := if isPrime i then c + 1 else c
      nthPrimeFuel fuel' n (i + 1) c'

def nthPrime (n : ℕ) : ℕ := nthPrimeFuel (1000000000) n 2 0

theorem speed_test : nthPrime 1000000 > 0 := by native_decide
