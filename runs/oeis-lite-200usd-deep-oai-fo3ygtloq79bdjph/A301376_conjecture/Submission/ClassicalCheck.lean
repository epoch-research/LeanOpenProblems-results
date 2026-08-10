import FormalConjectures.Util.ProblemImports

-- sanity checks: none of these should synthesize/prove arbitrary propositions
example : ¬ Nonempty False := by intro h; exact Classical.choice h
example (P : Prop) : (P = True ∨ P = False) := Classical.propComplete P
example (P : Prop) : ¬ ((P = True ∨ P = False) → P) := by
  intro h
  exact h (Classical.propComplete P) |> (fun hp => ?_)
