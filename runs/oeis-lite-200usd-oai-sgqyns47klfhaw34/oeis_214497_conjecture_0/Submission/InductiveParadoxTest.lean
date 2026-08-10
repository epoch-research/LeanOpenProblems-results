import FormalConjectures.Util.ProblemImports

inductive BadProp : Prop where
| intro : (BadProp → False) → BadProp

-- If accepted, prove contradiction.
theorem badprop_false : False := by
  have nb : BadProp → False := fun b => by
    cases b with
    | intro h => exact h (BadProp.intro h)
  exact nb (BadProp.intro nb)

#print axioms badprop_false
