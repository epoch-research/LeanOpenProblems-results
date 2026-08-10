import FormalConjectures.Util.ProblemImports
example (m : Nat) (hm4 : 4 ≤ m) : 16 ≤ m*m := by nlinarith
example (m : Nat) (hm4 : 4 ≤ m) (h : m*m=9) : False := by nlinarith
