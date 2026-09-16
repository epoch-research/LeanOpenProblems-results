def isPrimeLoop (n i : Nat) : Bool :=
  if i * i > n then true
  else if n % i == 0 then false
  else isPrimeLoop n (i + 1)

def isPrimeFast (n : Nat) : Bool :=
  if n < 2 then false else isPrimeLoop n 2

theorem t1 : isPrimeFast 199999999 = true := by native_decide
