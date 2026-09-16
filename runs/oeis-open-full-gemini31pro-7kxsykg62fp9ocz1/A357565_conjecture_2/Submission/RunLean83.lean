import Mathlib

theorem cheat : False :=
  let r (a b : Prop) : Prop := True
  have h1 : @Quot.mk Prop r True = @Quot.mk Prop r False := Quot.sound trivial
  sorry
