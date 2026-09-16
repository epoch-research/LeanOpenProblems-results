import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if i * i > n then true
      else if n % i == 0 then false
      else loop (i + 1)
    loop 2
  termination_by n - i -- just a hack

def nthPrime (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) (c : ℕ) : ℕ :=
    if c > n then i - 1
    else loop (i + 1) (c + if isPrime i then 1 else 0)
  loop 2 0

def A_seq : ℕ → ℕ
  | 0 => 0
  | 1 => nthPrime 0
  | k + 2 => nthPrime (k + 1) - A_seq (k + 1)

#eval A_seq 1
#eval A_seq 2
#eval A_seq 3
#eval A_seq 4
#eval A_seq 5
#eval A_seq 6
