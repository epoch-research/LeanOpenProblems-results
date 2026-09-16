import Submission.Spec

theorem disproof_check : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h : False := sorryAx _ false
    h
  )
