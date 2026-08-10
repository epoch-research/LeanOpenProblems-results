import Submission.Spec

#check Nat.sInf_def
#check Nat.sInf_eq_zero
#check csInf_eq_of_forall_ge_of_forall_gt_exists_lt
#check Nat.find
#eval collatz_step 3
example : A006577_steps 1 = 0 := by native_decide
example : A006577_steps 2 = 1 := by native_decide
example : A153330 1 = 1 := by native_decide

