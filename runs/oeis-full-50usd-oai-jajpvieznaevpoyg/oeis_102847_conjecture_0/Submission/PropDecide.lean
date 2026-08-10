import FormalConjectures.Util.ProblemImports

def P : Prop := ∃ n : Nat, n = n
#check inferInstanceAs (Decidable (P = True))
#check inferInstanceAs (Decidable P)
example : P = True := by native_decide
