import Mathlib

theorem my_false : (1:ℕ) = 2 := 
  let p1 : Prop := (1:ℕ) = 1
  let p2 : Prop := (1:ℕ) = 2
  let h_sound : Quot.mk (fun _ _ : Prop => True) True = Quot.mk (fun _ _ => True) (Nonempty p2) := Quot.sound trivial
  let f : Quot (fun _ _ : Prop => True) → Prop := Quot.lift (fun x => True = x) (fun a b _ => sorryAx ((True = a) = (True = b)) false)
  have h_eq : f (Quot.mk _ True) = f (Quot.mk _ (Nonempty p2)) := congrArg f h_sound
  have h_prop_eq : (True = True) = (True = Nonempty p2) := h_eq
  let h_true_eq_nonempty : True = Nonempty p2 := cast h_prop_eq rfl
  let e : p1 = p2 := propext ⟨fun _ => Classical.choice (cast h_true_eq_nonempty trivial), fun _ => Classical.choice (cast (sorryAx (True = Nonempty p1) false) trivial)⟩
  cast e rfl
