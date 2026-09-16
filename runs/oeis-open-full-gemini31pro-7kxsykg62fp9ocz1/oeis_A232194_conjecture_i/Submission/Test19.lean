import FormalConjectures.Util.ProblemImports

def f (A B C : Prop) : Prop := A ∧ B ↔ C
def g (A B C : Prop) : Prop := A ∧ (B ↔ C)
def h (A B C : Prop) : Prop := (A ∧ B) ↔ C

#check fun A B C => A ∧ B ↔ C
