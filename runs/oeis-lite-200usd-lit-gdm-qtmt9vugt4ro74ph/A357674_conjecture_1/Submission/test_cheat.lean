import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (P : Prop) (q : Q) : Type :=
  if q = Quot.mk R True then P else Prop

-- We want to define f P A : β P (Quot.mk R A)
-- If A = False, β P (Quot.mk R False) is definitionally Prop (since Quot.mk R False = Quot.mk R True is not defeq).
-- If A = True, we can cast from β P (Quot.mk R False).
noncomputable def f (P : Prop) (A : Prop) : β P (Quot.mk R A) := by
  by_cases hA : A = True
  · subst hA
    -- We need β P (Quot.mk R True), which is P.
    -- But we can cast from β P (Quot.mk R False), which is Prop.
    have h_eq : Quot.mk R True = Quot.mk R False := Quot.sound (by trivial)
    have h_type : β P (Quot.mk R True) = β P (Quot.mk R False) := by rw [h_eq]
    have h_false : β P (Quot.mk R False) = Prop := by
      dsimp [β]
      -- Since Quot.mk R False = Quot.mk R True is not defeq, but is it false?
      -- Wait, if it is not defeq, how do we reduce the if?
      -- We can do by_cases on the condition!
      sorry
  · sorry
