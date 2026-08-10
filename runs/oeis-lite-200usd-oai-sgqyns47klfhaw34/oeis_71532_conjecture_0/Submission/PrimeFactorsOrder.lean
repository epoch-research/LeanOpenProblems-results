import FormalConjectures.Util.ProblemImports
example : (12:ℕ).primeFactors = ({3,2} : Finset ℕ) := by simp
example : (18:ℕ).primeFactors = ({3,2} : Finset ℕ) := by simp
example : (30:ℕ).primeFactors = ({5,3,2} : Finset ℕ) := by simp
#print axioms PrimeFactorsOrder._example_1
