import FormalConjectures.Util.ProblemImports

example (P : Prop) : P := by
  classical
  -- Since Prop is finite, P is either True or False.
  have hc := Classical.propComplete P
  rcases hc with hT | hF
  · simpa [hT]
  · -- Need contradiction from P=False; finite/nontrivial Prop alone does not help.
    have hne : (True : Prop) ≠ False := true_ne_false
    have hcard : Fintype.card Prop = 2 := by native_decide
    exact?

example (P : Prop) : Nonempty P := by
  classical
  exact?

example (P : Prop) : P := by
  classical
  let e := Equiv.propEquivBool
  let b := e P
  cases b <;> simp [Equiv.propEquivBool] at *
  exact?
