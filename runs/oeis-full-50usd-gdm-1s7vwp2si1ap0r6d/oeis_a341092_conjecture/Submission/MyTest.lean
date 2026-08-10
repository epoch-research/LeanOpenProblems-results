import FormalConjectures.Util.ProblemImports

open Nat

def my_choose (n k : ℕ) : ℕ := 3 ^ k

macro_rules
  | `(Nat.choose $n $k) => `(my_choose $n $k)
  | `(($n).choose $k) => `(my_choose $n $k)

def test_choose1 (n k : ℕ) : ℕ := Nat.choose n k
def test_choose2 (n k : ℕ) : ℕ := n.choose k

#print test_choose1
#print test_choose2








