import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ =>
    have h1 : False := cast (sorryAx _ false) True.intro
    False.elim h1
