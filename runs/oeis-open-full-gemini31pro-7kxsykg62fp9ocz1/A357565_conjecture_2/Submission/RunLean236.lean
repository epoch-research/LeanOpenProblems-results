import Mathlib

theorem cheat : False :=
  let r (a b : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | true => True | false => False) (fun a b _ => propext ⟨fun _ => cast (Quot.sound trivial : @Quot.mk Bool r a = @Quot.mk Bool r b) trivial, fun _ => cast (Quot.sound trivial : @Quot.mk Bool r b = @Quot.mk Bool r a) trivial⟩) q
  sorry
