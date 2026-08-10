import FormalConjectures.Util.ProblemImports
partial def decFalse (_ : Unit) : Decidable False := decFalse ()

example : decFalse () = Decidable.isFalse (False.elim) := by
  apply Subsingleton.elim

theorem noBad : ¬ False := by intro h; exact h

-- Can we cast isFalse to isTrue via equality of Decidable False?
theorem bad : False := by
  have hEq : decFalse () = Decidable.isTrue (by exact False.elim (by exact False.elim (by contradiction))) := by
    apply Subsingleton.elim
  cases decFalse () with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h ?_)
  · sorry
#print axioms bad
