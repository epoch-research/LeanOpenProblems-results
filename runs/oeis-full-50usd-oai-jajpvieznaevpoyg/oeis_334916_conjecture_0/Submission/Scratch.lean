import Submission.Spec

#eval Nat.digits 6 160
#eval (Nat.digits 6 160).reverse
#eval baseless_value_list ((Nat.digits 6 160).reverse)
#eval is_baseless 6 160
#eval Nat.digits 10 8385
#eval baseless_value_list ((Nat.digits 10 8385).reverse)
#eval is_baseless 10 8385

example : is_baseless 6 160 := by native_decide
example : is_baseless 10 8385 := by native_decide
