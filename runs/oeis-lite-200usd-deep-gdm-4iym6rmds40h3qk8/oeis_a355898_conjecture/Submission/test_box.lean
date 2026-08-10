import Mathlib

inductive G_box (P : Prop) : Type where
  | mk : P → G_box P
  | fake : (G_box P → Empty) → G_box P

instance (P : Prop) : Nonempty (G_box P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨G_box.mk hp⟩
  · have h_empty : G_box P → Empty := by
      intro b
      induction b with
      | mk p => exact (h_not p).elim
      | fake f => exact f (G_box.fake f) -- wait, does this loop?
    exact ⟨G_box.fake h_empty⟩
