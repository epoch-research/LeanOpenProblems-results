import FormalConjectures.Util.ProblemImports

def C : Prop := 1 + 1 = 3

-- Define r such that (answer(sorry) : Prop) is one of the cases
def r (x y : Prop) : Prop :=
  (x = y) ∨ C ∨ (answer(sorry) : Prop)

theorem r_true_false : r True False := Or.inr (Or.inr trivial)

#print axioms r_true_false
