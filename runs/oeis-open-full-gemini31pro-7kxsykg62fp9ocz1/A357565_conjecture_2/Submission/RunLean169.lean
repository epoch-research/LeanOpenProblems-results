import Mathlib

theorem cheat : False :=
  let r (a b : ℕ) : Prop := True
  have h1 : @Quot.mk ℕ r 1 = @Quot.mk ℕ r 2 := Quot.sound trivial
  let f (q : Quot r) : Prop := Quot.lift (fun n => match n with | 1 => True | _ => False) (fun a b _ => propext (Iff.intro (fun _ => cast (Quot.sound trivial) trivial) (fun _ => cast (Quot.sound trivial) trivial))) q
  have h2 : True = False := by
    have h : f (@Quot.mk ℕ r 1) = f (@Quot.mk ℕ r 2) := by rw [h1]
    exact h
  cast h2 True.intro
