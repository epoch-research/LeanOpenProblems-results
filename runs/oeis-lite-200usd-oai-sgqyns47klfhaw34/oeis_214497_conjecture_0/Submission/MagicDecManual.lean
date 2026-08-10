import FormalConjectures.Util.ProblemImports

partial def magicDecidable (P : Prop) : Decidable P :=
  .isTrue (by
    let d : Decidable P := magicDecidable P
    cases d with
    | isTrue h => exact h
    | isFalse hn =>
        -- no h
        exact False.elim (hn (by exact ?_)))
