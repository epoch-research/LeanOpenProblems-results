import FormalConjectures.Util.ProblemImports

def P0 : Prop := ∃ x : ℤ, x = 0
def P1 : Prop := ∃ x : ℤ, x = 1

theorem try_eq (h0 : P0) (h1 : P1) : Classical.choose h0 = Classical.choose h1 := by
  have iff01 : P0 ↔ P1 := ⟨fun _ => h1, fun _ => h0⟩
  have e : P0 = P1 := propext iff01
  have hc : cast e h0 = h1 := Subsingleton.elim _ _
  -- #check congrArg Classical.choose hc
  fail_if_success exact congrArg Classical.choose hc
  -- try cases e?
  subst e
  sorry
