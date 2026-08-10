import FormalConjectures.Util.ProblemImports

theorem propComplete_does_not_help (P : Prop) : (P = True ∨ P = False) := Classical.propComplete P

-- The only branch that proves P is the `P=True` branch; `P=False` branch remains exactly ¬P.
example (P : Prop) : P = True → P := by intro h; exact Eq.mp h.symm True.intro
example (P : Prop) : P = False → ¬ P := by intro h hp; exact Eq.mp h hp
