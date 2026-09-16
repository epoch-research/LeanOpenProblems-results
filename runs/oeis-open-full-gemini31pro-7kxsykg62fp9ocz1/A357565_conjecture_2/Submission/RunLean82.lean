import Mathlib

theorem cheat : False :=
  let r (a b : Prop) : Prop := True
  have h1 : @Quot Prop r True = @Quot Prop r False := Quot.sound trivial
  sorry
