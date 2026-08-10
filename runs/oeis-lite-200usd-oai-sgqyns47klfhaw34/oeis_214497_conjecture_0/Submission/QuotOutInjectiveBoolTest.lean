import FormalConjectures.Util.ProblemImports

instance univSetoidBool : Setoid Bool where
  r := fun _ _ => True
  iseqv := ⟨by intro; trivial, by intro; trivial, by intro; trivial⟩

example : (⟦true⟧ : Quotient univSetoidBool) = ⟦false⟧ := Quotient.sound True.intro

example : Quotient.out (⟦true⟧ : Quotient univSetoidBool) = Quotient.out (⟦false⟧ : Quotient univSetoidBool) := by
  rw [Quotient.out_inj]
  exact Quotient.sound True.intro

-- This should not reduce to true = false.
example : False := by
  have h : Quotient.out (⟦true⟧ : Quotient univSetoidBool) = Quotient.out (⟦false⟧ : Quotient univSetoidBool) := by
    rw [Quotient.out_inj]
    exact Quotient.sound True.intro
  -- cannot `change true=false` because outs are opaque representatives.
  fail_if_success change true = false at h
  exact False.elim (by contradiction)
