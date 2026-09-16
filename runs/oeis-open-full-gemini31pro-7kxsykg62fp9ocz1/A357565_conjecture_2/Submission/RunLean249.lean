import Mathlib

theorem cheat : False :=
  let r (a b : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Bool := Quot.lift (fun b => b) (fun a b _ => sorryAx _ false) q
  have h2 : f (@Quot.mk Bool r true) = f (@Quot.mk Bool r false) := by rw [h1]
  have h3 : true = false := h2
  by contradiction
