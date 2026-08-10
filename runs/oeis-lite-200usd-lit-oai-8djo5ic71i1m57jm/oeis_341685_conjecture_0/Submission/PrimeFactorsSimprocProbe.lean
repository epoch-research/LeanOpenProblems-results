import FormalConjectures.Util.ProblemImports

example : Nat.primeFactors 4 = {2} := by simp

example : Nat.primeFactors 4 ≠ ({3} : Finset ℕ) := by native_decide

example : False := by
  have h : Nat.primeFactors 4 = ({3} : Finset ℕ) := by
    simp
  native_decide at h

