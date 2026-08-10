import FormalConjectures.Util.ProblemImports

def P0 : ℤ → Prop := fun x => x = 0
def P1 : ℤ → Prop := fun x => x = 1

example {P Q : ℤ → Prop} (hp : ∃ x, P x) (hq : ∃ x, Q x) : Classical.choose hp = Classical.choose hq := by
  have iffpq : (∃ x, P x) ↔ (∃ x, Q x) := ⟨fun _ => hq, fun _ => hp⟩
  have e : (∃ x, P x) = (∃ x, Q x) := propext iffpq
  have hc : cast e hp = hq := proof_irrel _ _
  -- try prove choose cast equals choose original
  have hcast : Classical.choose (cast e hp) = Classical.choose hp := by
    cases e
    rfl
  rw [← hc]
  exact hcast

example : (0:ℤ)=1 := by
  have h0 : ∃ x, P0 x := ⟨0,rfl⟩
  have h1 : ∃ x, P1 x := ⟨1,rfl⟩
  have hc : Classical.choose h0 = Classical.choose h1 := by
    have iff01 : (∃ x, P0 x) ↔ (∃ x, P1 x) := ⟨fun _ => h1, fun _ => h0⟩
    have e : (∃ x, P0 x) = (∃ x, P1 x) := propext iff01
    have hpr : cast e h0 = h1 := proof_irrel _ _
    have hcast : Classical.choose (cast e h0) = Classical.choose h0 := by
      cases e
      rfl
    rw [← hpr]
    exact hcast
  have s0 := Classical.choose_spec h0
  have s1 := Classical.choose_spec h1
  rw [← s0, ← s1]
  exact hc
