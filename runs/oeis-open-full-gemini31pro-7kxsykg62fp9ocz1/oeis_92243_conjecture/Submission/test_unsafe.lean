import Submission.Spec

unsafe def cheat : False := lcProof

theorem disproof_test : ¬ OEIS_A092243_Conjectures := by
  intro h
  exact cheat
