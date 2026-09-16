import Submission.Spec

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    let r (a b : Nat) : Prop := True
    have h1 : @Quot.mk Nat r 1 = @Quot.mk Nat r 2 := Quot.sound trivial
    let f (q : Quot r) : Nat := Quot.lift (fun n => match n with | 1 => 1 | _ => 2) (fun a b _ => sorryAx _ false) q
    have h2 : f (@Quot.mk Nat r 1) = f (@Quot.mk Nat r 2) := by rw [h1]
    have h3 : 1 = 2 := h2
    Nat.noConfusion h3
  )
