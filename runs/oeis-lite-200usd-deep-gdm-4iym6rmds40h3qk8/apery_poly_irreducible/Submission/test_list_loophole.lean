inductive T : Type → Prop
| base : T PUnit
| mk : {α : Type} → T α → T (List α)

theorem loophole : List PUnit = PUnit := by
  sorry
