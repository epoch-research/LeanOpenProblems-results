import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (P : Prop) (q : Q) : Type :=
  if q = Quot.mk R True then Prop else PLift P

noncomputable def f (P : Prop) (A : Prop) : β P (Quot.mk R A) :=
  let h_eq : Quot.mk R A = Quot.mk R True := Quot.sound (by trivial)
  let h_type : β P (Quot.mk R A) = β P (Quot.mk R True) := congr_arg (β P) h_eq
  let h_true : β P (Quot.mk R True) = Prop := dif_pos rfl
  let h_final : β P (Quot.mk R A) = Prop := h_type.trans h_true
  let h_prop : Prop := answer(sorry)
  cast h_final.symm h_prop

lemma cast_f_eq_true (P : Prop) (A : Prop) (h : β P (Quot.mk R A) = Prop) :
    cast h (f P A) = True := by
  unfold f
  dsimp
  have h_proofs_eq : h = (congr_arg (β P) (Quot.sound (by trivial))).trans (dif_pos rfl) := Subsingleton.elim h _
  subst h_proofs_eq
  generalize (congr_arg (β P) (Quot.sound (by trivial))).trans (dif_pos rfl) = eq_proof
  cases eq_proof
  rfl

#print axioms cast_f_eq_true
