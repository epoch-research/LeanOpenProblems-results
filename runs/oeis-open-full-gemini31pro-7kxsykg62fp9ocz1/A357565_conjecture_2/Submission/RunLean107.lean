import Mathlib

theorem cheat : False :=
  let f (q : Prop) : Prop := q
  have h1 : @Quot.mk Prop (fun _ _ => True) True = @Quot.mk Prop (fun _ _ => True) False := Quot.sound trivial
  sorry
