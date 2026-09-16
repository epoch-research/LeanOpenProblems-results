import Mathlib

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : ℕ) : Bool :=
      if h : i * i > n then true
      else if n % i == 0 then false
      else loop (i + 1)
    termination_by n - i
    decreasing_by omega
    loop 2

def sumPrimes (n : ℕ) : ℕ :=
  let rec loop (i : ℕ) (c : ℕ) (sum : ℕ) : ℕ :=
    if h : c >= n then sum
    else
      have h_is : (if isPrime i then 1 else 0) ≤ 1 := by split <;> omega
      loop (i + 1) (c + if isPrime i then 1 else 0) (sum + if isPrime i then i else 0)
  termination_by n - c
  decreasing_by
    -- omega doesn't know about the if directly here unless we simplify
    sorry
  loop 2 0 0

theorem test_100 : sumPrimes 100 > 0 := by sorry
