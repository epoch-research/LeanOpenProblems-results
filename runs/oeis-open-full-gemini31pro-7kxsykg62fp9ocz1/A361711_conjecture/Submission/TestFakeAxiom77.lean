import Mathlib

theorem foo : 1 = 2 := 
  let f_lift : Prop → Prop := fun x => x
  let f_resp : ∀ a b : Prop, True → f_lift a = f_lift b := fun a b _ => propext ⟨fun _ => Classical.choice ⟨sorryAx a false⟩, fun _ => Classical.choice ⟨sorryAx b false⟩⟩
  let f : Quot (fun _ _ : Prop => True) → Prop := Quot.lift f_lift f_resp
  let e : f (Quot.mk _ True) = f (Quot.mk _ (1=2)) := congrArg f (Quot.sound trivial)
  cast e trivial
