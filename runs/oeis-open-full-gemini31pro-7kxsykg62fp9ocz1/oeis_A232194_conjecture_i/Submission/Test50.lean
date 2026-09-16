import FormalConjectures.Util.ProblemImports

def P1 (A B C : Prop) : Prop := A ∧ (B ↔ C)
def P2 (A B C : Prop) : Prop := (A ∧ B) ↔ C
def P3 (A B C : Prop) : Prop := A ∧ B ↔ C

theorem t1 : P3 = P1 := rfl
theorem t2 : P3 = P2 := rfl
