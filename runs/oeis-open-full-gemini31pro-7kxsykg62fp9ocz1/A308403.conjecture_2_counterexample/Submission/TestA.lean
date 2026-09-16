import Mathlib

partial def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : ℕ) :=
      if i * i > n then true
      else if n % i == 0 then false
      else loop (i + 1)
    loop 2

partial def nthPrime (n : ℕ) : ℕ :=
  let rec loop (i count : ℕ) :=
    if isPrime i then
      if count == n then i
      else loop (i + 1) (count + 1)
    else loop (i + 1) count
  loop 2 0

def A008347_seq_comp : ℕ → ℕ
  | 0 => 0
  | 1 => nthPrime 0
  | k + 2 => nthPrime (k + 1) - A008347_seq_comp (k + 1)

#eval A008347_seq_comp 10
