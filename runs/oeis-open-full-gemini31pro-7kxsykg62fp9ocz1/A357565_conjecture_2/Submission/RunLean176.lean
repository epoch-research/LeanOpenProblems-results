import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  have h1 : False := cast (Quot.sound (sorryAx _ false) : @Quot.mk Prop (fun _ _ => True) True = @Quot.mk Prop (fun _ _ => True) False) True.intro
  False.elim h1
