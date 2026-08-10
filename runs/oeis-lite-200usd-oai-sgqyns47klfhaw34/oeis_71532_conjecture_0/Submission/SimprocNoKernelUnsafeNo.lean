import FormalConjectures.Util.ProblemImports
-- no skip-kernel; see if exact generated proof term can be saved through a def, not theorem
example : (12:ℕ).primeFactors = ({3,2} : Finset ℕ) := by
  change ({3,2} : Finset ℕ) = ({3,2} : Finset ℕ)
  rfl
