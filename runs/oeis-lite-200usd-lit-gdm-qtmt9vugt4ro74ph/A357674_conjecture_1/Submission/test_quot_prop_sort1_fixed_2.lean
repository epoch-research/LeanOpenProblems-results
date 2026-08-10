import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (P : Prop) (q : Q) : Type :=
  if q = Quot.mk R True then Prop else PLift P

noncomputable def f (P : Prop) (A : Prop) : β P (Quot.mk R A) := by
  have h_eq : Quot.mk R A = Quot.mk R True := Quot.sound (by trivial)
  have h_type : β P (Quot.mk R A) = β P (Quot.mk R True) := by rw [h_eq]
  have h_true : β P (Quot.mk R True) = Prop := by
    dsimp [β]
    rw [if_pos rfl]
  have h_final : β P (Quot.mk R A) = Prop := h_type.trans h_true
  have h_prop : Prop := answer(sorry)
  exact cast h_final.symm h_prop

#print axioms f
