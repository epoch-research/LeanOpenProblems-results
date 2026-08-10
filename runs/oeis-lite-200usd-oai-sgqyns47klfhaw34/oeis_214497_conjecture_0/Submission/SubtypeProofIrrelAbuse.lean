import FormalConjectures.Util.ProblemImports

example : ({x : Nat // True}) := ⟨0, True.intro⟩
example : (⟨0, True.intro⟩ : {x : Nat // True}) ≠ ⟨1, True.intro⟩ := by intro h; cases h

example : False := by
  have h : (⟨0, True.intro⟩ : {x : Nat // True}) = ⟨1, True.intro⟩ := by
    -- proof irrelevance doesn't apply to subtype values in Type
    exact?
  cases h
