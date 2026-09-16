import Mathlib.Data.Nat.Factors

open Nat List

def findDivisorHelper (l : List ℕ) (acc : ℕ) (target : ℕ) : ℕ :=
  if acc ≥ target then acc
  else match l with
  | [] => acc
  | p :: ps => findDivisorHelper ps (acc * p) target

def findDivisor (m : ℕ) (target : ℕ) : ℕ :=
  findDivisorHelper (Nat.factors m) 1 target
