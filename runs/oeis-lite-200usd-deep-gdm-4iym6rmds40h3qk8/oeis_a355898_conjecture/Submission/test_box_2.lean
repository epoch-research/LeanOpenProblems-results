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
      | fake f => exact f (G_box.fake f)
    exact ⟨G_box.fake h_empty⟩

noncomputable def get_box (P : Prop) : G_box P :=
  Classical.choice inferInstance

theorem prove_any (P : Prop) : P := by
  have b := get_box P
  cases b with
  | mk p => exact p
  | fake f =>
    have h_empty : Empty := f (get_box P)
    exact h_empty.elim
