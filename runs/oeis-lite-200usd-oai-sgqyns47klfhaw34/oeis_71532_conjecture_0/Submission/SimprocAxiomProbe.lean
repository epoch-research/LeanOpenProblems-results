import FormalConjectures.Util.ProblemImports

set_option debug.skipKernelTC false

theorem pf12 : (12:ℕ).primeFactors = ({3,2} : Finset ℕ) := by
  native_decide
#print axioms pf12

theorem pf12simp : (12:ℕ).primeFactors = ({3,2} : Finset ℕ) := by
  -- expected kernel mismatch if simproc faulty
  simp
#print axioms pf12simp
