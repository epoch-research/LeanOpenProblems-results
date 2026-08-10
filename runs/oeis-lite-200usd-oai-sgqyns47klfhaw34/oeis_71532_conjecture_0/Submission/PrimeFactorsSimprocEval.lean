import FormalConjectures.Util.ProblemImports
example : (12:ℕ).primeFactors = ({2,3} : Finset ℕ) := by simp
example : (1:ℕ).primeFactors = (∅ : Finset ℕ) := by simp
example : (2:ℕ).primeFactors = ({2} : Finset ℕ) := by simp
example : (4:ℕ).primeFactors = ({2} : Finset ℕ) := by simp
example : False := by
  have h : (4:ℕ).primeFactors = ({3} : Finset ℕ) := by simp
  have : 3 ∈ (4:ℕ).primeFactors := by simpa [h]
  exact (Nat.not_prime_one ?) -- dummy
