import Mathlib

theorem foo : 1 = 2 :=
  @Quot.sound Prop (fun x y => (1:ℕ) = 2) True False sorry
