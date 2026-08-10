import FormalConjectures.Util.ProblemImports
axiom P : Prop

example : P := by
  let rec h : P := h
  exact h

example : P := by
  let rec d : Decidable P := Decidable.isTrue h
      where h : P := by
        cases d with
        | isTrue hp => exact hp
        | isFalse hn => exact False.elim (hn h)
  cases d with
  | isTrue hp => exact hp
  | isFalse hn => exact False.elim (hn (by exact (by cases d with | isTrue hp => exact hp | isFalse hn => exact False.elim (hn (Classical.choice ?_)))))
