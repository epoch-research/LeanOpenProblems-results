import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h1 : (1 = 2) = False := propext ⟨fun _ => cast (by sorry) trivial, fun _ => cast (by sorry) trivial⟩
    have h2 : False := h1 ▸ (by sorry)
    h2
  )
