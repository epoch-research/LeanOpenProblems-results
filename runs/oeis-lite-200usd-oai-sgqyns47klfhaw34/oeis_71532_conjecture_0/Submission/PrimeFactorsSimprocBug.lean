import FormalConjectures.Util.ProblemImports

-- Try false primeFactors equalities with simp using custom simproc.
example : (0:ℕ).primeFactors = ({2} : Finset ℕ) := by
  simp

example : False := by
  have h : (0:ℕ).primeFactors = ({2} : Finset ℕ) := by simp
  have : 2 ∈ (0:ℕ).primeFactors := by simpa [h]
  simpa [Nat.mem_primeFactors] using this

#print axioms PrimeFactorsSimprocBug._example_2
