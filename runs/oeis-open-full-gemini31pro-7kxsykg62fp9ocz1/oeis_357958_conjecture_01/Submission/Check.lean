import Submission.Spec

def isPrime (n : ℕ) : Bool :=
  if n < 2 then false
  else Id.run do
    for i in [2:n] do
      if n % i == 0 then return false
    return true

def check (p : ℕ) : Bool :=
  if p < 5 ∨ !isPrime p then true
  else
    (a p) % (p^5) == 39

def main : IO Unit := do
  for p in [5:100] do
    if isPrime p then
      let res := check p
      IO.println s!"p={p}, check={res}"
      if !res then
        IO.println s!"Counterexample found: {p}"
