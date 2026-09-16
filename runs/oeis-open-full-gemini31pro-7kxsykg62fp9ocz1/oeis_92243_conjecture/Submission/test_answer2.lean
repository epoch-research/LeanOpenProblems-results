import Submission.Spec
open Google

theorem oeis_92243_conjecture.disproof_test : ¬ (type_of% @oeis_92243_conjecture) := by
  intro h
  exact answer(sorry)
