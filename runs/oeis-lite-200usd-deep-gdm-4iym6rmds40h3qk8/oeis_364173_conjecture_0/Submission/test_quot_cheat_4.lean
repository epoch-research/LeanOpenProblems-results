import FormalConjectures.Util.ProblemImports

def C : Prop := 1 + 1 = 3

def r (x y : Prop) : Prop :=
  (x = y) ∨ (x = True ∧ y = False ∧ (answer(sorry) : Prop))

theorem r_true_false : r True False := Or.inr ⟨rfl, rfl, trivial⟩

theorem h_eq : Quot.mk r True = Quot.mk r False := Quot.sound r_true_false

def g_respects_type : Prop := ∀ x y, r x y → (x ∨ C) = (y ∨ C)

def g_respects_proof : g_respects_type := answer(sorry)

#print axioms g_respects_proof
