import FormalConjectures.Util.ProblemImports
opaque f (n : Nat) : Nat := n+1

def b (n : Nat) : Bool := f n == n+1
#eval b 10
example : b 10 = true := by native_decide
