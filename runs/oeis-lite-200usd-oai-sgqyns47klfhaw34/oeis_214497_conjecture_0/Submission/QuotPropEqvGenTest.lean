import FormalConjectures.Util.ProblemImports

abbrev Alpha : Prop := True ∨ True

def aa : Alpha := Or.inl True.intro
def bb : Alpha := Or.inr True.intro

def rempty : Alpha → Alpha → Prop := fun _ _ => False

example : (Quot.mk rempty aa : Quot rempty) = Quot.mk rempty bb := by
  apply Subsingleton.elim

example : Relation.EqvGen rempty aa bb := by
  apply Quot.eqvGen_exact
  apply Subsingleton.elim

-- Can EqvGen of the empty relation between the two Or constructors imply False?
example : Relation.EqvGen rempty aa bb → False := by
  intro h
  induction h with
  | rel h => exact h
  | refl =>
      -- goal is False in case aa=bb? see if no_confusion works
      simp [aa, bb] at *
  | symm _ ih => exact ih
  | trans _ _ ih1 ih2 => exact ih1
