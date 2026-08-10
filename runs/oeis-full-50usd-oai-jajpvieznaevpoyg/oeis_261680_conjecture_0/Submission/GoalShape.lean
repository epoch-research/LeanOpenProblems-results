import FormalConjectures.Util.ProblemImports
open Nat List Finset

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun u =>
    Finset.sum (Finset.range (n - u + 1)) fun v =>
      Finset.sum (Finset.range (n - (u + v) + 1)) fun w =>
        let x := n - (u + v + w)
        if is_binary_palindrome u ∧ is_binary_palindrome v ∧ is_binary_palindrome w ∧ is_binary_palindrome x
        then 1 else 0

example (n : Nat) : a n > 0 := by
  simp [a, is_binary_palindrome]
