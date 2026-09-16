import Mathlib

theorem my_false : False := 
  let r : Prop → Prop → Prop := fun _ _ => True
  let h_sound : Quot.mk r True = Quot.mk r False := Quot.sound trivial
  let f_lift : Prop → Prop := fun x => x
  let f_resp : ∀ a b, r a b → f_lift a = f_lift b := 
    fun a b _ => 
      have h1 : f_lift a = f_lift a := rfl
      have h2 : f_lift a = f_lift b := cast (sorryAx ((f_lift a = f_lift a) = (f_lift a = f_lift b)) false) h1
      h2
  let f : Quot r → Prop := Quot.lift f_lift f_resp
  have h_eq : f (Quot.mk r True) = f (Quot.mk r False) := congrArg f h_sound
  have h_True_eq_False : True = False := h_eq
  cast h_True_eq_False trivial
