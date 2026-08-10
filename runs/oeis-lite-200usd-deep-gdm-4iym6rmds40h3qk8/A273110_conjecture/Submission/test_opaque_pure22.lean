import FormalConjectures.Util.ProblemImports

-- Let's define a relation `R` on `Nat`:
def R (x y : Nat) : Prop :=
  x = 1 ∧ y = 0

-- Is `R` well-founded?
-- Yes, because the only transition is 1 -> 0, and there are no infinite chains!
-- Let's prove that `R` is well-founded!
theorem wf_R : WellFounded R := by
  sorry
