import FormalConjectures.Util.ProblemImports

partial def decTrue (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    let rec h : P := by
      cases decTrue P with
      | isTrue hp => exact hp
      | isFalse hn => exact False.elim (hn h)
    exact h)

#print decTrue
#reduce decTrue True

theorem arbitrary (P : Prop) : P := by
  -- if decTrue unfolds to isTrue, this should work maybe
  change P
  have d := decTrue P
  cases d with
  | isTrue h => exact h
  | isFalse hn =>
      -- use definition? try simp/whnf
      exact False.elim (hn (by
        let rec h : P := by
          cases decTrue P with
          | isTrue hp => exact hp
          | isFalse hn => exact False.elim (hn h)
        exact h))

#print axioms decTrue
#print axioms arbitrary
