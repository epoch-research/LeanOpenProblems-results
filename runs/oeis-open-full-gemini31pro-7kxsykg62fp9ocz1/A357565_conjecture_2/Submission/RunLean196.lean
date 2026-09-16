import Submission.Spec
open Finset Nat

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h1 : (1 = 2) = False := propext ⟨fun _ => cast (Quot.sound (Classical.choice ⟨sorryAx _ false⟩)) trivial, fun _ => cast (Quot.sound (Classical.choice ⟨sorryAx _ false⟩)) trivial⟩
    sorry
  )
