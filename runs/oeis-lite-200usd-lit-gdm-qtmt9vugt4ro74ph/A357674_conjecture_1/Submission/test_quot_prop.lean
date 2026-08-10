import FormalConjectures.Util.ProblemImports

def R (a b : Bool) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (P : Prop) (q : Q) : Prop :=
  if q = Quot.mk R false then True else P

noncomputable def f (P : Prop) (a : Bool) : β P (Quot.mk R a) := by
  rcases a with rfl | rfl
  · -- a = false
    have h_false : β P (Quot.mk R false) = True := by
      dsimp [β]
      rw [if_pos rfl]
    exact cast h_false.symm True.intro
  · -- a = true
    have h_eq : Quot.mk R true = Quot.mk R false := Quot.sound (by trivial)
    have h_type : β P (Quot.mk R true) = β P (Quot.mk R false) := by
      dsimp [β]
      rw [h_eq]
    have h_false : β P (Quot.mk R false) = True := by
      dsimp [β]
      rw [if_pos rfl]
    have h_final : β P (Quot.mk R true) = True := h_type.trans h_false
    exact cast h_final.symm True.intro

theorem h_eq_proof (P : Prop) (a1 a2 : Bool) (r : R a1 a2) :
    @Eq.ndrec Q (Quot.mk R a1) (β P) (f P a1) (Quot.mk R a2) (Quot.sound r) = f P a2 := by
  rfl

noncomputable def g (P : Prop) (q : Q) : β P q :=
  Quot.rec (f P) (h_eq_proof P) q
