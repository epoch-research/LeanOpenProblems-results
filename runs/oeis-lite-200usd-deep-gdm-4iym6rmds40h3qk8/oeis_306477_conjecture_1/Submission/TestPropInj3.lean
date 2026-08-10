import Mathlib.Tactic.Congr!

theorem prop_subtype_eq_inj (P1 P2 : Prop) (h : { y : Prop // y = P1 } = { y : Prop // y = P2 }) : P1 ↔ P2 := by
  constructor
  · intro hP1
    let val1 : { y : Prop // y = P1 } := ⟨P1, rfl⟩
    let val2 : { y : Prop // y = P2 } := cast h val1
    have h_eq : val2.val = val1.val := by
      dsimp [val2]
      congr!
    have h_val1 : val1.val = P1 := rfl
    rw [h_val1] at h_eq
    have h_prop := val2.property
    rw [h_eq] at h_prop
    rw [← h_prop]
    exact hP1
  · sorry
