import FormalConjectures.Util.ProblemImports

def P4 (A B C : Prop) : Prop := A ∧ (B ↔ C)
def P5 (A B C : Prop) : Prop := (A) ∧ (B ↔ C)

theorem t3 : P4 = P5 := rfl
