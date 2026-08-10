import FormalConjectures.Util.ProblemImports
def cnt : Nat → Nat → Nat
  | 0, acc => acc
  | (n+1), acc => cnt n (acc+1)
set_option maxRecDepth 4000000 in
example : cnt 1000000 0 = 1000000 := by decide
