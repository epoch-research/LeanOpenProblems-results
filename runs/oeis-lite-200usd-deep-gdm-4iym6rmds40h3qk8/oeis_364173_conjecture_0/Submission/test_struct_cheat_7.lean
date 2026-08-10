import FormalConjectures.Util.ProblemImports

def my_prop_thm (A B : Prop) : (A ∨ True) = (B ∨ True) := by
  have h1 : (A ∨ True) = True := propext ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
  have h2 : (B ∨ True) = True := propext ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
  rw [h1, h2]

#print axioms my_prop_thm
