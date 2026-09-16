import Mathlib

open Matrix Nat

def isPrimeDecidable (n : ℕ) : Decidable n.Prime := inferInstance

def M (n : ℕ) : List (List ℤ) :=
  (List.range n).map fun i =>
    (List.range n).map fun j =>
      if (i + 1)^2 + (j + 1)^2 |>.Prime then 1 else 0

#eval M 6
