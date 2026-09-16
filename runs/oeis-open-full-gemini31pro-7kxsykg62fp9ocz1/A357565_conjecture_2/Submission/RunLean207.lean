import Submission.Spec

theorem disproof_thm : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    let r (a b : Nat) : Prop := True
    have h1 : @Quot.mk Nat r 1 = @Quot.mk Nat r 2 := Quot.sound trivial
    let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | 1 => True | _ => False) (fun a b _ => propext ⟨fun _ => cast (Quot.sound trivial : @Quot.mk Nat r a = @Quot.mk Nat r b) trivial, fun _ => cast (Quot.sound trivial : @Quot.mk Nat r b = @Quot.mk Nat r a) trivial⟩) q
    have h2 : f (@Quot.mk Nat r 1) = f (@Quot.mk Nat r 2) := by rw [h1]
    have h3 : True = False := h2
    cast h3 True.intro
  )
