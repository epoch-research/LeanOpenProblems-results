def isPrimeLoop (n : Nat) (i : Nat) : Bool :=
  if h : i * i > n then true
  else if n % i == 0 then false
  else isPrimeLoop n (i + 1)
termination_by n - i

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else isPrimeLoop n 2

def countPrimes (n : Nat) : Nat :=
  let rec loop (i : Nat) (acc : Nat) : Nat :=
    if h : i > n then acc
    else loop (i + 1) (if isPrime i then acc + 1 else acc)
  loop 0 0
termination_by n - i

-- Let's test decide
theorem test_decide : countPrimes 500 = 95 := by decide
