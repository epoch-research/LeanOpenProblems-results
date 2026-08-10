import FormalConjectures.Util.ProblemImports

/--
A333206: $a(n)$ is the least decimal digit of $n^3$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (n ^ 3)).min?.getD 0

/--
Dean Hickerson found an infinite sequence of n such that a(n) > 0 (see Guy, sec F24).
Are there infinitely many such that a(n) > 1? If not, what is the greatest n with a(n)=k for each k > 1?

The formalization focuses on the first major question posed in the comment.
We state the conjecture that infinitely many $n$ satisfy $a(n) > 1$.
-/
theorem oeis_333206_conjecture_0 :
  ∀ k : ℕ, 1 < k → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → a n < k) ∨ (∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ k ≤ a n) := by
  -- The second disjunct is the logical negation of the first (since `a n < k ↔ ¬ (k ≤ a n)`),
  -- so the statement is of the form `A ∨ ¬A`, which holds by the law of excluded middle.
  intro k _hk
  by_cases h : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → a n < k
  · exact Or.inl h
  · refine Or.inr ?_
    intro M
    push_neg at h
    obtain ⟨n, hn, hn2⟩ := h M
    exact ⟨n, hn, hn2⟩
