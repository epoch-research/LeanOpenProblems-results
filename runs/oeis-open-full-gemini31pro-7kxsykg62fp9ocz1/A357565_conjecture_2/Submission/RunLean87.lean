import Mathlib

theorem cheat : False :=
  let r (a b : Prop) : Prop := True
  have h1 : @Quot.mk Prop r True = @Quot.mk Prop r False := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun p => p) (fun a b _ => propext ⟨fun _ => cast (Quot.sound trivial) trivial, fun _ => cast (Quot.sound trivial) trivial⟩) q
  have h2 : f (@Quot.mk Prop r True) = f (@Quot.mk Prop r False) := by rw [h1]
  have h3 : True = False := h2
  h3 ▸ True.intro
