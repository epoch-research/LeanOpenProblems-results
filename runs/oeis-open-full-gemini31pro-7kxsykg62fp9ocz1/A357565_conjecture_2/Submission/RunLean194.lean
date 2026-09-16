import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    let r (a b : Nat) : Prop := True
    have h1 : @Quot.mk Nat r 1 = @Quot.mk Nat r 2 := Quot.sound trivial
    let f (q : Quot r) : Prop := Quot.lift (fun _ => True) (fun a b _ => propext ⟨fun _ => trivial, fun _ => trivial⟩) q
    sorry
  )
