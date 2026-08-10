import FormalConjectures.Util.ProblemImports
open Nat

theorem rec_shape (n : ℕ) (hn : n > 0) : ∃ k : ℕ, True := by
  induction n with
  | zero => omega
  | succ n ih => exact ⟨0, trivial⟩

-- Can call recursively on smaller n in theorem proof?
theorem rec_call_smaller (n : ℕ) (hn : n > 0) : True := by
  cases n with
  | zero => omega
  | succ n =>
      by_cases h : n > 0
      · exact rec_call_smaller n h
      · trivial

#print axioms rec_call_smaller
