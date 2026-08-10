import FormalConjectures.Util.ProblemImports

example : False := by simp
example (x y : Nat) : x = y := by ext
example (P : Prop) : P := by aesop
