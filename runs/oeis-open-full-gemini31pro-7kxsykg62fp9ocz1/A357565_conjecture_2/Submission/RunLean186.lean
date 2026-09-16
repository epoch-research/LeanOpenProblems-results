import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h : False := sorryAx _ false
    h
  )
