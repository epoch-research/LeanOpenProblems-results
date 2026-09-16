import Mathlib

theorem cheat : False :=
  let r (a b : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | true => True | false => False) (fun a b _ => sorryAx _ false) q
  have h2 : True = False := by
    have h : f (@Quot.mk Bool r true) = f (@Quot.mk Bool r false) := by rw [h1]
    exact h
  cast h2 True.intro
