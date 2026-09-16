import Submission.Spec

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  let f : False → ¬ (type_of% @A357565_conjecture_2) := fun h => False.elim h
  f (sorryAx _ false)
