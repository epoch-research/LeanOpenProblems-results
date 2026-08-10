import FormalConjectures.Util.ProblemImports

inductive Bad : Bool → Type
| mk : Bad false  -- Bad true is empty now

def R (a b : Bool) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (q : Q) : Type :=
  if q = Quot.mk R false then Bad false else Bad true

noncomputable def f (a : Bool) : β (Quot.mk R a) := by
  rcases a with rfl | rfl
  · -- a = false
    have h_false : β (Quot.mk R false) = Bad false := by
      dsimp [β]
      rw [if_pos rfl]
    exact cast h_false.symm Bad.mk
  · -- a = true
    have h_eq : Quot.mk R true = Quot.mk R false := Quot.sound (by trivial)
    have h_type : β (Quot.mk R true) = β (Quot.mk R false) := by
      dsimp [β]
      rw [h_eq]
    have h_false : β (Quot.mk R false) = Bad false := by
      dsimp [β]
      rw [if_pos rfl]
    have h_final : β (Quot.mk R true) = Bad false := h_type.trans h_false
    exact cast h_final.symm Bad.mk

theorem h_eq_proof (a1 a2 : Bool) (r : R a1 a2) :
    @Eq.ndrec Q (Quot.mk R a1) β (f a1) (Quot.mk R a2) (Quot.sound r) = f a2 := by
  have h_eq : Quot.mk R a1 = Quot.mk R a2 := Quot.sound r
  unfold Eq.ndrec
  have h_p2 : β (Quot.mk R a2) = Bad false := by
    have : Quot.mk R a2 = Quot.mk R false := Quot.sound (by trivial)
    dsimp [β]
    rw [this, if_pos rfl]
  apply (cast_inj h_p2).mp
  have h_eq_bad (x y : Bad false) : x = y := by
    cases x
    cases y
    rfl
  apply h_eq_bad

noncomputable def g : (q : Q) → β q :=
  Quot.rec f h_eq_proof

-- Let us try to prove False
theorem prove_false : False := by
  have h_val := g (Quot.mk R true)
  -- The type of h_val is β (Quot.mk R true)
  -- Since we have h_eq : Quot.mk R true = Quot.mk R false
  -- β (Quot.mk R true) is Bad false.
  -- But wait, what if we use the fact that true != false to show β (Quot.mk R true) = Bad true?
  -- Can we prove Quot.mk R true != Quot.mk R false?
  -- No, because we can prove they are equal!
  sorry
