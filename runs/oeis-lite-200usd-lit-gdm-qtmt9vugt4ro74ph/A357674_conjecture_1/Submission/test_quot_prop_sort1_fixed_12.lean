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

lemma cast_cast_symm {α β : Type} (h : α = β) (x : β) : cast h (cast h.symm x) = x := by
  cases h
  rfl

lemma cast_f_eq_true (P : Prop) (A : Prop) (h : β P (Quot.mk R A) = Prop) :
    cast h (f P A) = True := by
  unfold f
  dsimp
  have h_final : (congr_arg (β P) (Quot.sound (by trivial))).trans (dif_pos rfl) = h := Subsingleton.elim _ _
  rw [← h_final]
  exact cast_cast_symm _ True

lemma cast_cast_val {α β γ : Type} (h1 : α = β) (h2 : β = γ) (x : α) : cast h2 (cast h1 x) = cast (h1.trans h2) x := by
  cases h1
  rfl

theorem h_eq_proof (P : Prop) (A1 A2 : Prop) (r : R A1 A2) :
    @Eq.ndrec Q (Quot.mk R A1) (β P) (f P A1) (Quot.mk R A2) (Quot.sound r) = f P A2 := by
  have h_p2 : β P (Quot.mk R A2) = Prop := by
    have : Quot.mk R A2 = Quot.mk R True := Quot.sound (by trivial)
    dsimp [β]
    rw [this, if_pos rfl]
  apply (cast_inj h_p2).mp
  have h_ndrec : @Eq.ndrec Q (Quot.mk R A1) (β P) (f P A1) (Quot.mk R A2) (Quot.sound r) =
      cast (congr_arg (β P) (Quot.sound r)) (f P A1) := rfl
  rw [h_ndrec]
  rw [cast_cast_val]
  rw [cast_f_eq_true P A1]
  rw [cast_f_eq_true P A2]

noncomputable def g (P : Prop) (q : Q) : β P q :=
  Quot.rec (f P) (h_eq_proof P) q

#print axioms g
