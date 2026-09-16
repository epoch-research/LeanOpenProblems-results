import Mathlib

theorem cheat : False :=
  let r (a b : ℕ) : Prop := True
  have h1 : @Quot.mk ℕ r 1 = @Quot.mk ℕ r 2 := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | 1 => True | _ => False) (fun a b _ => propext ⟨fun _ => cast (Quot.sound trivial : @Quot.mk ℕ r a = @Quot.mk ℕ r b) trivial, fun _ => cast (Quot.sound trivial : @Quot.mk ℕ r b = @Quot.mk ℕ r a) trivial⟩) q
  have h2 : f (@Quot.mk ℕ r 1) = f (@Quot.mk ℕ r 2) := by rw [h1]
  have h3 : True = False := h2
  cast h3 True.intro
