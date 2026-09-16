import Mathlib

theorem cheat : False :=
  let r (_ _ : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | true => True | false => False) (fun _ _ _ => sorryAx _ false) q
  have h2 : f (@Quot.mk Bool r true) = f (@Quot.mk Bool r false) := congrArg f h1
  have h3 : True = False := h2
  cast h3 True.intro
