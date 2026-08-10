import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  match Classical.dec P with
  | isTrue h => exact h
  | isFalse h =>
      -- h : ¬P, cannot synthesize P
      exact False.elim (h (by
        match Classical.dec P with
        | isTrue hp => exact hp
        | isFalse hn => exact False.elim ?x))

example (P : Prop) : ¬P → P := by
  intro hn
  match Classical.dec P with
  | isTrue hp => exact hp
  | isFalse hn2 => exact False.elim ?bad
