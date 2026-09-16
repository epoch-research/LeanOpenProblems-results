import FormalConjectures.Util.ProblemImports

def P6 (A B C : Prop) : Prop := A → B ∧ C
def P7 (A B C : Prop) : Prop := A → (B ∧ C)
def P8 (A B C : Prop) : Prop := (A → B) ∧ C

theorem t4 : P6 = P7 := rfl
theorem t5 : P6 = P8 := rfl
