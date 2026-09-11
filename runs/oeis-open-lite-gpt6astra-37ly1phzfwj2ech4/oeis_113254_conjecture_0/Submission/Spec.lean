import FormalConjectures.Util.ProblemImports

open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

private def squareRootSeq (n : ℕ) : ℤ :=
  match n with
  | 0 => 2
  | 1 => 56
  | n + 2 => -4 * squareRootSeq (n + 1) - 64 * squareRootSeq n

private lemma a_step_six (n : ℕ) :
    a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  have h0 : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := by
    rw [a]
  have h1 : a (n + 5) = -4 * a (n + 4) + 256 * a (n + 2) + 4096 * a (n + 1) := by
    simpa [Nat.add_assoc] using (show a ((n + 1) + 4) =
      -4 * a ((n + 1) + 3) + 256 * a ((n + 1) + 1) + 4096 * a (n + 1) from by rw [a])
  have h2 : a (n + 6) = -4 * a (n + 5) + 256 * a (n + 3) + 4096 * a (n + 2) := by
    simpa [Nat.add_assoc] using (show a ((n + 2) + 4) =
      -4 * a ((n + 2) + 3) + 256 * a ((n + 2) + 1) + 4096 * a (n + 2) from by rw [a])
  linear_combination 64 * h0 - 4 * h1 + h2

private lemma squareRootSeq_step (n : ℕ) :
    squareRootSeq (n + 3) ^ 2 = -48 * squareRootSeq (n + 2) ^ 2 +
      3072 * squareRootSeq (n + 1) ^ 2 + 262144 * squareRootSeq n ^ 2 := by
  have h : squareRootSeq (n + 3) =
      -4 * squareRootSeq (n + 2) - 64 * squareRootSeq (n + 1) := by
    simpa [Nat.add_assoc] using (show squareRootSeq ((n + 1) + 2) =
      -4 * squareRootSeq ((n + 1) + 1) - 64 * squareRootSeq (n + 1) from by rw [squareRootSeq])
  rw [h, show squareRootSeq (n + 2) =
    -4 * squareRootSeq (n + 1) - 64 * squareRootSeq n from by rw [squareRootSeq]]
  ring

private lemma a_odd_square (n : ℕ) : a (2 * n + 1) = squareRootSeq n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | (_ | n))
    · norm_num [a, squareRootSeq]
    · norm_num [a, squareRootSeq]
    · norm_num [a, squareRootSeq]
    · have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h := a_step_six (2 * n + 1)
      have e0 : 2 * (n + 1 + 1 + 1) + 1 = (2 * n + 1) + 6 := by omega
      have e1 : (2 * n + 1) + 4 = 2 * (n + 2) + 1 := by omega
      have e2 : (2 * n + 1) + 2 = 2 * (n + 1) + 1 := by omega
      rw [e0, h, e1, e2, h0, h1, h2]
      exact (squareRootSeq_step n).symm

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨squareRootSeq n, by simpa [pow_two] using a_odd_square n⟩

theorem oeis_113254_conjecture_0.disproof : ¬ (type_of% @oeis_113254_conjecture_0) := sorry
