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

def nthPrime (n : ℕ) : ℕ := nthPrimeFuel 1000 n 2 0

def S_seq : ℕ → ℕ
  | 0 => 0
  | 1 => nthPrime 0
  | k + 2 => nthPrime (k + 1) - S_seq (k + 1)

#eval S_seq 1
#eval S_seq 2
#eval S_seq 3
#eval S_seq 4
#eval S_seq 5
#eval S_seq 6
#eval S_seq 7
#eval S_seq 8
