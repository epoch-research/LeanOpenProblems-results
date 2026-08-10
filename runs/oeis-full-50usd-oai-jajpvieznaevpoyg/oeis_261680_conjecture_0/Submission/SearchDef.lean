import FormalConjectures.Util.ProblemImports
open Nat List Finset

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

def findRep (n : Nat) : Option (Nat × Nat × Nat × Nat) := Id.run do
  for u in [0:n+1] do
    for v in [0:n+1-u] do
      for w in [0:n+1-u-v] do
        let x := n - (u+v+w)
        if is_binary_palindrome u && is_binary_palindrome v && is_binary_palindrome w && is_binary_palindrome x then
          return some (u,v,w,x)
  return none

#eval (List.range 50).all (fun n => (findRep n).isSome)
example : (findRep 1000).isSome = true := by native_decide
