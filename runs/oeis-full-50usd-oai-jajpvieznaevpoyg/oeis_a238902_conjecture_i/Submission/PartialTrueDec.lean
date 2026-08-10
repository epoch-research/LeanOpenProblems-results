import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) (_ : Unit) : Decidable P :=
  Decidable.isTrue (by
    have d := decP P ()
    cases d with
    | isTrue h => exact h
    | isFalse h => exact False.elim (h (by
        have d2 := decP P ()
        cases d2 with
        | isTrue h2 => exact h2
        | isFalse h2 => exact False.elim (h2 (by
            have d3 := decP P ()
            cases d3 with
            | isTrue h3 => exact h3
            | isFalse h3 => exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact False.elim (h3 (by exact h3)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

#print axioms decP

 theorem badFalse : False := by
  have d := decP False ()
  cases d with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by
      have d2 := decP False ()
      cases d2 with
      | isTrue h2 => exact h2
      | isFalse h2 => exact False.elim (h2 (by exact badFalse)))
#print axioms badFalse
