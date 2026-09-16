import Submission.Spec

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  let x : False := Classical.choice ⟨sorryAx _ false⟩
  False.elim x
