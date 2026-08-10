import FormalConjectures.Util.ProblemImports

def trueDec (P : Prop) : Decidable P := by
  let rec d : Decidable P := Decidable.isTrue (by
    cases d with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn (by
        cases d with
        | isTrue h => exact h
        | isFalse hn2 => exact False.elim (hn2 (by
            cases d with
            | isTrue h => exact h
            | isFalse hn3 => exact False.elim (hn3 (by
                cases d with
                | isTrue h => exact h
                | isFalse hn4 => exact False.elim (hn4 (by
                    cases d with
                    | isTrue h => exact h
                    | isFalse hn5 => exact False.elim (hn5 (by exact False.elim (hn (by contradiction)))))))))))
  exact d

theorem arbitrary (P : Prop) : P := by
  cases trueDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by cases trueDec P with | isTrue h => exact h | isFalse hn2 => exact False.elim (hn2 (by contradiction))))
#print axioms trueDec
#print axioms arbitrary
