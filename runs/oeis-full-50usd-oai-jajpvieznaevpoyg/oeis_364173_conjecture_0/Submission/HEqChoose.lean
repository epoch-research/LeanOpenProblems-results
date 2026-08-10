import FormalConjectures.Util.ProblemImports

example {P Q : ℤ → Prop} (hp : ∃ x, P x) (hq : ∃ x, Q x) : Classical.choose hp = Classical.choose hq := by
  have hh : HEq hp hq := proof_irrel_heq hp hq
  cases hh
  rfl

-- If this works, it is alarming; test contradiction with concrete exists.
def P0 : ℤ → Prop := fun x => x = 0
def P1 : ℤ → Prop := fun x => x = 1
example (h0 : ∃ x, P0 x) (h1 : ∃ x, P1 x) : Classical.choose h0 = Classical.choose h1 := by
  have hh : HEq h0 h1 := proof_irrel_heq h0 h1
  cases hh
  rfl
example : (0:ℤ)=1 := by
  have h0 : ∃ x, P0 x := ⟨0,rfl⟩
  have h1 : ∃ x, P1 x := ⟨1,rfl⟩
  have hc : Classical.choose h0 = Classical.choose h1 := by
    have hh : HEq h0 h1 := proof_irrel_heq h0 h1
    cases hh
    rfl
  have s0 := Classical.choose_spec h0
  have s1 := Classical.choose_spec h1
  rw [← s0, ← s1]
  exact hc
#print axioms HEqChoose._example_1
