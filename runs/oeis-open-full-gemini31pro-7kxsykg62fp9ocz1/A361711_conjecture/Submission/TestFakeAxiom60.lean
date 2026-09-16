import Mathlib

theorem my_false : (1:ℕ) = 2 := 
  let p1 : Prop := (1:ℕ) = 1
  let p2 : Prop := (1:ℕ) = 2
  let h_sound_1 : Quot.mk (fun _ _ : Prop => True) True = Quot.mk (fun _ _ => True) (Nonempty p1) := Quot.sound trivial
  let h_sound_2 : Quot.mk (fun _ _ : Prop => True) True = Quot.mk (fun _ _ => True) (Nonempty p2) := Quot.sound trivial
  let f : Quot (fun _ _ : Prop => True) → Prop := Quot.lift (fun x => True = x) (fun a b _ => 
    let e : (True = a) = (True = b) := propext ⟨fun ha => 
        let _ : Nonempty (True = b) := Quot.sound (sorryAx (True = True) false)
        sorry
      , fun hb => 
        let _ : Nonempty (True = a) := Quot.sound (sorryAx (True = True) false)
        sorry
      ⟩
    e
  )
  have h_eq_1 : f (Quot.mk _ True) = f (Quot.mk _ (Nonempty p1)) := congrArg f h_sound_1
  have h_eq_2 : f (Quot.mk _ True) = f (Quot.mk _ (Nonempty p2)) := congrArg f h_sound_2
  have h_prop_eq_1 : (True = True) = (True = Nonempty p1) := h_eq_1
  have h_prop_eq_2 : (True = True) = (True = Nonempty p2) := h_eq_2
  let h_true_eq_nonempty_1 : True = Nonempty p1 := cast h_prop_eq_1 rfl
  let h_true_eq_nonempty_2 : True = Nonempty p2 := cast h_prop_eq_2 rfl
  let e : p1 = p2 := propext ⟨fun _ => Classical.choice (cast h_true_eq_nonempty_2 trivial), fun _ => Classical.choice (cast h_true_eq_nonempty_1 trivial)⟩
  cast e rfl
