import FormalConjectures.Util.ProblemImports
partial def f (n : Nat) : Nat := f n
example (n : Nat) : f n = f n := rfl
example (n : Nat) : 0 ≤ f n := Nat.zero_le _
#print axioms f
