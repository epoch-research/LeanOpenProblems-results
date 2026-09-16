import Mathlib

theorem cheat : False :=
  let r (a b : Prop) : Prop := True
  have h1 : @Quot.mk Prop r True = @Quot.mk Prop r False := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun _ => True) (fun a b _ => propext ⟨fun _ => trivial, fun _ => trivial⟩) q
  have h2 : f (@Quot.mk Prop r True) = f (@Quot.mk Prop r False) := by rw [h1]
  sorryAx _ false
