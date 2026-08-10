import FormalConjectures.Util.ProblemImports

partial def v : Nat → Prop
| 0 => v 0 → False
| _+1 => True
#print v
#print axioms v
#reduce v 0
example : False := by
  -- Does v unfold? likely not
  have h1 : v 0 → False := by
    intro hv
    -- if hv : v0 and v0 = v0 -> False, apply?
    exact ?_
  exact ?_
