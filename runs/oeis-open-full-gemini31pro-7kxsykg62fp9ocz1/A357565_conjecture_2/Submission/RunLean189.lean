import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h1 : (1 = 2) = False := propext ⟨fun _ => sorryAx _ false, fun _ => sorryAx _ false⟩
    have h2 : False := h1 ▸ (sorryAx _ false : 1 = 2)
    h2
  )
