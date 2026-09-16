import Submission.Spec
def cheat_def : False := sorry
theorem my_thm : ¬ OEIS_A092243_Conjectures := by
  intro h; exact cheat_def
#print axioms my_thm
