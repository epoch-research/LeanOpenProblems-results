import Mathlib

theorem foo : False :=
  let r : Prop → Prop → Prop := fun _ _ => True
  have hr : ∀ a b, r a b := fun _ _ => trivial
  have h_eq : Quot r = Quot r := rfl
  have f : (Quot.mk r True) = (Quot.mk r False) := Quot.sound trivial
  sorry
