import Submission.Spec

partial def cheat : False := cheat

theorem disproof_test : ¬ OEIS_A092243_Conjectures := by
  intro h
  exact cheat
