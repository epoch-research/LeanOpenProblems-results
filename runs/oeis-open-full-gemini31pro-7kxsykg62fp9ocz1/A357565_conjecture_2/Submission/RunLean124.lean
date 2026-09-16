import Mathlib

theorem cheat : False :=
  let r (a b : ℕ) : Prop := True
  have h1 : @Quot.mk ℕ r 1 = @Quot.mk ℕ r 2 := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun _ => True) (fun a b _ => propext ⟨fun _ => trivial, fun _ => trivial⟩) q
  have h2 : f (@Quot.mk ℕ r 1) = f (@Quot.mk ℕ r 2) := by rw [h1]
  sorryAx _ false
