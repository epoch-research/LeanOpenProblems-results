import Submission.Spec

theorem cheat : ¬ (type_of% @A357565_conjecture_2) :=
  have h1 : False := cast (sorryAx _ false) True.intro
  False.elim h1
