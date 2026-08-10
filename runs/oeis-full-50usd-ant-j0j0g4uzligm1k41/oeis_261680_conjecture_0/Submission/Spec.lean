import FormalConjectures.Util.ProblemImports

open Nat List Finset

/-- The predicate for a number to be a binary palindrome (OEIS A006995), defined to return Bool. -/
def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

/--
A261680: Number of ordered quadruples $(u,v,w,x)$ of binary palindromes (see A006995) with $u+v+w+x=n$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun u =>
    Finset.sum (Finset.range (n - u + 1)) fun v =>
      Finset.sum (Finset.range (n - (u + v) + 1)) fun w =>
        let x := n - (u + v + w)
        if is_binary_palindrome u ∧
           is_binary_palindrome v ∧
           is_binary_palindrome w ∧
           is_binary_palindrome x
        then 1 else 0

/-- OEIS A261680 Conjecture: a(n)>0: every number is the sum of four binary palindromes. -/
theorem oeis_261680_conjecture_0 (n : ℕ) : a n > 0 := by
  sorry
