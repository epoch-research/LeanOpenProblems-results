import FormalConjectures.Util.ProblemImports

partial def decFalse (_ : Unit) : Decidable False := decFalse ()
#print axioms decFalse
#check decFalse

theorem badFromPartialDec : False := by
  have d := decFalse ()
  cases d with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by
      have d2 := decFalse ()
      cases d2 with
      | isTrue h2 => exact h2
      | isFalse h2 => exact False.elim (h2 (by exact badFromPartialDec))))
#print axioms badFromPartialDec
