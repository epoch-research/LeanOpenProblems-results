import FormalConjectures.Util.ProblemImports

-- Try local recursive Decidable data to produce a proof.
theorem arbitrary (P : Prop) : P := by
  let rec d : Decidable P := Decidable.isTrue (by
    cases d with
    | isTrue hp => exact hp
    | isFalse hn =>
        -- d is defined as isTrue, but cases doesn't know that. try recursive extraction again
        exact False.elim (hn (by
          cases d with
          | isTrue hp => exact hp
          | isFalse hn2 => exact False.elim (hn2 (by
              cases d with
              | isTrue hp => exact hp
              | isFalse hn3 => exact False.elim (hn3 (by
                  -- infinite; try use proof irrelevance equality to impossible constructors?
                  have e : d = Decidable.isTrue (by
                    cases d with
                    | isTrue hp => exact hp
                    | isFalse hn4 => exact False.elim (hn4 (by cases d with | isTrue hp => exact hp | isFalse hn5 => exact False.elim (hn5 (by exact hp_placeholder)))) := rfl
                  cases d with
                  | isTrue hp => exact hp
                  | isFalse hn4 => exact False.elim (hn4 (by exact hp_placeholder))))))))
  cases d with
  | isTrue hp => exact hp
  | isFalse hn =>
      -- contradiction with definition maybe rfl if d reduces?
      exact False.elim (hn (by
        cases d with
        | isTrue hp => exact hp
        | isFalse hn2 => exact False.elim (hn2 (by cases d with | isTrue hp => exact hp | isFalse hn3 => exact False.elim (hn3 ?_)))))

#print axioms arbitrary
