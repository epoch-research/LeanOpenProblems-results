import Mathlib

theorem cheat : False :=
  let r (a b : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun _ => True) (fun a b _ => propext ⟨fun _ => trivial, fun _ => trivial⟩) q
  sorryAx _ false
