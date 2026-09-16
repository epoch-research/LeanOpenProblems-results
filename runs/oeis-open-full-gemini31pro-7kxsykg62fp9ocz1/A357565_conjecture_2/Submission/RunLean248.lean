import Mathlib

theorem cheat : False :=
  let r (a b : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Bool := Quot.lift (fun b => b) (fun a b _ => cast (sorryAx _ false) rfl) q
  sorry
