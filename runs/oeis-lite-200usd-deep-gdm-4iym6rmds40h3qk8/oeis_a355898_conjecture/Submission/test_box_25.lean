import Mathlib

theorem test_neg (P : Prop) : ¬ (¬ ¬ ¬ ¬ (P ↔ ¬P)) := by
  have hR : ¬ (P ↔ ¬P) := by
    intro h
    have hp : ¬P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  intro hT
  have h_not_S : ¬ ¬ ¬ (P ↔ ¬P) := by
    intro hS
    exact hS hR
  exact hT h_not_S
