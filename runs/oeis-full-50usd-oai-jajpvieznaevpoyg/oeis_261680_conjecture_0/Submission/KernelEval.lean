import FormalConjectures.Util.ProblemImports

def f (n : Nat) : Nat := (List.range (n+1)).foldl (fun s i => s+i) 0
example : f 10 = 55 := by rfl
#print axioms f
