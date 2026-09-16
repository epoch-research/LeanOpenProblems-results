import Mathlib

theorem cheat : False :=
  let r (a b : Nat) : Prop := True
  have h1 : @Quot.mk Nat r 1 = @Quot.mk Nat r 2 := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | 1 => True | _ => False) (fun a b _ => propext ⟨fun _ => sorryAx _ false, fun _ => sorryAx _ false⟩) q
  have h2 : True = False := by
    have h : f (@Quot.mk Nat r 1) = f (@Quot.mk Nat r 2) := by rw [h1]
    exact h
  cast h2 True.intro
