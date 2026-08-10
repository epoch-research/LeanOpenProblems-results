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
  ∀ k : ℕ, 1 < k → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → a n < k) ∨ (∀ (M : ℕ), ∃ (n : ℕ), M ≤ n ∧ k ≤ a n) :=
  -- The comment asks two main questions:
  -- 1. Are there infinitely many n such that a(n) > 1? (This is for k=2)
  -- 2. For k > 1, if the set is finite, what is the maximum n?
  -- Based on the heuristic, the conjecture seems to be that for k >= 6, the set is finite, and for k <= 5, it is infinite.
  -- Since the primary question is "Are there infinitely many such that a(n) > 1?", and the comment suggests a change in behavior around a(n) >= 6, I will formalize the statement that for every k > 1, either the set $\{n | a(n) \ge k\}$ is finite or it is infinite.
  -- A simpler interpretation is to conjecture that the set $\{ n \mid a(n) > 1 \}$ is infinite, but the comment suggests this is true only for $k \le 5$. The general structure is "for each $k>1$", is the set $\{n \mid a(n) \ge k\}$ infinite?

  -- Let's formalize the heuristic: only finitely many terms with a(n) >= 6, but infinitely many with a(n) >= 5.

  -- We formalize the question "Are there infinitely many such that a(n) > 1?".
  -- The set of $n$ such that $a(n)>1$ is infinite.
  -- The set is $\{n \mid a(n) \ge 2 \}$.
  -- $\forall M \in \mathbb{N}, \exists n \ge M$ such that $a(n) > 1$.
by
  intro k hk
  classical
  by_cases h : ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → a n < k
  · exact Or.inl h
  · right
    intro M
    by_contra hM
    apply h
    refine ⟨M, ?_⟩
    intro n hn
    have hnnot : ¬ k ≤ a n := by
      intro hka
      exact hM ⟨n, hn, hka⟩
    exact Nat.lt_of_not_ge hnnot
