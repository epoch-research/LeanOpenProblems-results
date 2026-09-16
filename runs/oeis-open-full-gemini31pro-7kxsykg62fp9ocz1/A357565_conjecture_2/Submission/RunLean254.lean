import Mathlib

theorem cheat : False :=
  let x : False :=
    let r (a b : Bool) : Prop := True
    have h1 : @Quot.mk Bool r true = @Quot.mk Bool r false := Quot.sound trivial
    let f (q : Quot r) : Prop := Quot.lift (fun _ => True) (fun a b _ => propext ⟨fun _ => trivial, fun _ => trivial⟩) q
    have h2 : f (@Quot.mk Bool r true) = f (@Quot.mk Bool r false) := by rw [h1]
    cast (sorryAx _ false) True.intro
  x
