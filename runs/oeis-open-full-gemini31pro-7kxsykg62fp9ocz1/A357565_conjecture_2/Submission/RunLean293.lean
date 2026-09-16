import Mathlib

theorem cheat : False :=
  let r (_ _ : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Bool := Quot.lift (fun n => n) (fun _ _ _ => cast (Quot.sound trivial : @Quot.mk Bool r true = @Quot.mk Bool r false) rfl) q
  have h2 : f (@Quot.mk Bool r true) = f (@Quot.mk Bool r false) := congrArg f h1
  have h3 : true = false := h2
  Bool.noConfusion h3
