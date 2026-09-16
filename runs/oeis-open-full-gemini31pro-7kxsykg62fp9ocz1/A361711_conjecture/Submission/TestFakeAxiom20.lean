import Mathlib

theorem foo : 1 = 2 :=
  let r : Prop → Prop → Prop := fun x y => (1:ℕ) = 2
  let h : Quot.mk r True = Quot.mk r False := @Quot.sound Prop r True False sorry
  sorry
