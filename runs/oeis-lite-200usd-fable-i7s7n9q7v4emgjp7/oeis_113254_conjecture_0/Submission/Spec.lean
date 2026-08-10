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

/-- The square-root sequence: `a (2*n+1) = (b n)^2`. -/
private def b (n : ℕ) : ℤ :=
  match n with
  | 0 => 2
  | 1 => 56
  | n' + 2 => -4 * b (n' + 1) - 64 * b n'

private lemma a_rec (n : ℕ) :
    a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := by
  rw [a]

private lemma b_rec (n : ℕ) :
    b (n + 2) = -4 * b (n + 1) - 64 * b n := by
  rw [b]

private lemma key : ∀ n : ℕ,
    a (2 * n + 1) = b n ^ 2 ∧ a (2 * n + 2) = b n * b (n + 1) + 64 ^ (n + 1)
      ∧ a (2 * n + 3) = b (n + 1) ^ 2
      ∧ a (2 * n + 4) = b (n + 1) * b (n + 2) + 64 ^ (n + 2) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [a, b]
  | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have h5 : a (2 * n + 5) = b (n + 2) ^ 2 := by
        have e : 2 * n + 5 = (2 * n + 1) + 4 := by ring
        rw [e, a_rec]
        have e1 : 2 * n + 1 + 3 = 2 * n + 4 := by ring
        have e2 : 2 * n + 1 + 1 = 2 * n + 2 := by ring
        rw [e1, e2, h4, h2, h1, b_rec]
        ring
      have h6 : a (2 * n + 6) = b (n + 2) * b (n + 3) + 64 ^ (n + 3) := by
        have e : 2 * n + 6 = (2 * n + 2) + 4 := by ring
        rw [e, a_rec]
        have e1 : 2 * n + 2 + 3 = 2 * n + 5 := by ring
        have e2 : 2 * n + 2 + 1 = 2 * n + 3 := by ring
        have eb : b (n + 3) = -4 * b (n + 2) - 64 * b (n + 1) := b_rec (n + 1)
        rw [e1, e2, h5, h3, h2, eb, b_rec]
        ring
      have e1 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
      have e2 : 2 * (n + 1) + 2 = 2 * n + 4 := by ring
      have e3 : 2 * (n + 1) + 3 = 2 * n + 5 := by ring
      have e4 : 2 * (n + 1) + 4 = 2 * n + 6 := by ring
      have e5 : n + 1 + 1 = n + 2 := rfl
      have e6 : n + 1 + 2 = n + 3 := rfl
      rw [e1, e2, e3, e4, e5, e6]
      exact ⟨h3, h4, h5, h6⟩

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨b n, by rw [(key n).1]; ring⟩
