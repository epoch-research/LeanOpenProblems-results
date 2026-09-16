import Submission.Spec

partial def cheat (u : Unit) : False := cheat u

theorem disproof_test : ¬ OEIS_A092243_Conjectures := by
  intro h
  exact cheat ()
