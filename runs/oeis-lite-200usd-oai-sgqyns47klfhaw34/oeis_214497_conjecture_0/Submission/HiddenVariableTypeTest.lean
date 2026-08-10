import FormalConjectures.Util.ProblemImports

section
variable (H : False)
theorem hidden_var_test : True := by
  exact False.elim H
#print hidden_var_test
#check hidden_var_test
end

section
variable {H : False}
theorem hidden_imp_test : True := by
  exact False.elim H
#print hidden_imp_test
#check hidden_imp_test
end
