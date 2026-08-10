import FormalConjectures.Util.ProblemImports
open Nat List Finset

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

example (m : Nat) : is_binary_palindrome (2^m - 1) := by
  simp [is_binary_palindrome]
