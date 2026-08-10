import FormalConjectures.Util.ProblemImports

partial def decTrue (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    cases decTrue P with
    | isTrue h => exact h
    | isFalse hn =>
        -- try to use the same decTrue proof recursively
        exact False.elim (hn (by
          cases decTrue P with
          | isTrue h => exact h
          | isFalse hn2 => exact False.elim (hn2 (by
              -- one more level?
              cases decTrue P with
              | isTrue h => exact h
              | isFalse hn3 => exact False.elim (hn3 (by exact Classical.choice (propComplete P))))))))

theorem arbitrary (P : Prop) : P := by
  cases decTrue P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by cases decTrue P with | isTrue h => exact h | isFalse hn2 => exact False.elim (hn2 ?_)))

#print axioms decTrue
#print axioms arbitrary
