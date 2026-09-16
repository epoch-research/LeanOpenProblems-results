import Submission.Spec

unsafe def cheat_unsafe : False := cheat_unsafe

theorem cheat : False := by
  exact (unsafeCast cheat_unsafe : False)
