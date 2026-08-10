import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad False
| mk {α : Prop} : Bad (α → False) → Bad α

def f : (α : Prop) → Bad α → (α → False)
| _, Bad.base => fun (h0 : False) => h0
| _, @Bad.mk α' h => f (α' → False) h

theorem h_eq : (True → False) = False := by
  have h_iff : (True → False) ↔ False := by
    apply Iff.intro
    · intro h
      exact h True.intro
    · intro f
      exact False.elim f
  exact propext h_iff

theorem false_proof : False := by
  have bad_false : Bad False := Bad.base
  have bad_not_true : Bad (True → False) := h_eq.symm ▸ bad_false
  have bad_true : Bad True := Bad.mk bad_not_true
  have f_res : True → False := f True bad_true
  exact f_res True.intro

#print axioms false_proof

#print axioms false_proof
