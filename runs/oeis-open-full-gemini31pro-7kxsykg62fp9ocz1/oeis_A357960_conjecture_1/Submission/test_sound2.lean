import Mathlib

theorem foo : False :=
  let r : Prop → Prop → Prop := fun _ _ => True
  have hr : ∀ a b, r a b := fun _ _ => trivial
  have f : (Quot.mk r True) = (Quot.mk r False) := Quot.sound trivial
  -- does this imply True = False? Not directly, it's about Quot
  sorry
