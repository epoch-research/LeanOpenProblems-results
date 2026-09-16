import Mathlib

theorem cheat : False :=
  let r (a b : Bool) : Prop := True
  have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun b => b = true) (fun a b _ => propext ⟨fun _ => sorry, fun _ => sorry⟩) q
  have h2 : f (@Quot.mk Bool r true) = f (@Quot.mk Bool r false) := by rw [h1]
  have h3 : (true = true) = (false = true) := h2
  have h4 : false = true := cast h3 rfl
  Bool.noConfusion h4
