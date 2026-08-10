import FormalConjectures.Util.ProblemImports
example (p n : ℕ) (h1 : (2*p+3)/3 ≤ n) (h2 : n ≤ p-1) : ∃ m, n = p-1-m ∧ 3*m+2 ≤ p := by
  refine ⟨p-1-n, ?_, ?_⟩
  · omega
  · omega
