import Mathlib
def main : IO Unit := do
  IO.println (Nat.divisors 0).card
  IO.println (Nat.divisors 12).card
