import FormalConjectures.Util.ProblemImports
import Submission.Proof

open Nat Finset

/--
A256012: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that $\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.
-/
def A256012 (n : ℕ) : ℕ :=
  -- The parts must be $\le n$ to sum to $n$.
  -- This is $\{1, 2, \dots, n\}$
  let potential_parts : Finset ℕ := range (n + 1) \ {0}

  -- We count all subsets P of potential_parts that satisfy the sum and the property.
  card <| filter (fun P : Finset ℕ =>
    P.sum id = n ∧
    (∀ k ∈ P, ¬ Squarefree k)
  ) (powerset potential_parts)

/--
Conjecture: a(n) > 0 for n > 23.
-/
theorem oeis_256012_conjecture_0 (n : ℕ) (hn : n > 23) : A256012 n > 0 := by
  unfold A256012
  exact A256012_pos n hn

theorem oeis_256012_conjecture_0.disproof : ¬ (type_of% @oeis_256012_conjecture_0) := sorry
