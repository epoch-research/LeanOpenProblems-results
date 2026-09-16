import FormalConjectures.Util.ProblemImports

def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n % 2 == 0 then n == 2
  else
    let rec check (d : ℕ) : Bool :=
      if d * d > n then true
      else if n % d == 0 then false
      else check (d + 2)
    check 3
termination_by isPrimeFast n => n
decreasing_by sorry

def nextPrimeFast (n : ℕ) : ℕ :=
  if isPrimeFast (n + 1) then n + 1
  else nextPrimeFast (n + 1)
termination_by nextPrimeFast n => 10000 - n -- just a fake bound
decreasing_by sorry

