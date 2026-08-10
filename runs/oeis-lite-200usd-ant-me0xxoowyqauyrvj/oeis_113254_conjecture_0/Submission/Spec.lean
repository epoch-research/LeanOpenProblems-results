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

/-- The square-root sequence: `c (n) = ±√(a (2*n+1))`, a second-order linear recurrence
with `c 0 = 2`, `c 1 = 56` and `c (n+2) = -4 * c (n+1) - 64 * c n`. -/
def c (n : ℕ) : ℤ :=
  match n with
  | 0 => 2
  | 1 => 56
  | n' + 2 => -4 * c (n' + 1) - 64 * c n'

/-- The defining recurrence for `a`. -/
private lemma hrec (n : ℕ) :
    a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := rfl

/-- The defining recurrence for `c`. -/
private lemma crec (n : ℕ) : c (n + 2) = -4 * c (n + 1) - 64 * c n := rfl

/-- The odd-indexed subsequence of `a` satisfies a third-order linear recurrence, which is a
consequence of the fourth-order recurrence for `a`. -/
private lemma oddrec (k : ℕ) :
    a (2 * k + 7) = -48 * a (2 * k + 5) + 3072 * a (2 * k + 3) + 262144 * a (2 * k + 1) := by
  have e0 : a (2 * k + 4) = -4 * a (2 * k + 3) + 256 * a (2 * k + 1) + 4096 * a (2 * k) :=
    hrec (2 * k)
  have e1 : a (2 * k + 5) = -4 * a (2 * k + 4) + 256 * a (2 * k + 2) + 4096 * a (2 * k + 1) :=
    hrec (2 * k + 1)
  have e2 : a (2 * k + 6) = -4 * a (2 * k + 5) + 256 * a (2 * k + 3) + 4096 * a (2 * k + 2) :=
    hrec (2 * k + 2)
  have e3 : a (2 * k + 7) = -4 * a (2 * k + 6) + 256 * a (2 * k + 4) + 4096 * a (2 * k + 3) :=
    hrec (2 * k + 3)
  rw [e3, e2, e1, e0]; ring

/-- The key identity: `a (2*n+1)` is the square of `c n`. -/
private theorem key : ∀ n, a (2 * n + 1) = (c n) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · decide
    · decide
    · decide
    · have h0 : a (2 * m + 1) = (c m) ^ 2 := ih m (by omega)
      have h1 : a (2 * m + 3) = (c (m + 1)) ^ 2 := by
        have := ih (m + 1) (by omega)
        rwa [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring] at this
      have h2 : a (2 * m + 5) = (c (m + 2)) ^ 2 := by
        have := ih (m + 2) (by omega)
        rwa [show 2 * (m + 2) + 1 = 2 * m + 5 from by ring] at this
      rw [show 2 * (m + 3) + 1 = 2 * m + 7 from by ring, oddrec m, h0, h1, h2,
        crec (m + 1), crec m]
      ring

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨c n, by rw [key n]; ring⟩
