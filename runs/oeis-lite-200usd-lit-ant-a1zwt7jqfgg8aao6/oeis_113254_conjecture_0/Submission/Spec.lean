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

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
-- The "square root" sequence: `c k` will satisfy `a (2*k+1) = (c k)^2`.
-- It is the second-order linear recurrence with characteristic roots `-2 ± 2√15 i`
-- (the complex roots of the characteristic polynomial of `a`).
def c (n : ℕ) : ℤ :=
  match n with
  | 0 => 2
  | 1 => 56
  | n' + 2 => -4 * c (n' + 1) - 64 * c n'

/-- The defining recurrence of `a`, packaged for `n ≥ 4`. -/
theorem a_rec (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := by
  rfl

/-- The defining recurrence of `c`. -/
theorem c_rec (n : ℕ) : c (n + 2) = -4 * c (n + 1) - 64 * c n := by
  rfl

/-- A "step by two" recurrence for `a`, obtained because the characteristic
polynomial `x⁴ + 4x³ - 256x - 4096` divides `x⁶ + 48x⁴ - 3072x² - 262144`
(with cofactor `x² - 4x + 64`). -/
theorem a_step2 (m : ℕ) :
    a (m + 6) = -48 * a (m + 4) + 3072 * a (m + 2) + 262144 * a m := by
  have h0 : a (m + 4) = -4 * a (m + 3) + 256 * a (m + 1) + 4096 * a m := a_rec m
  have h1 : a (m + 5) = -4 * a (m + 4) + 256 * a (m + 2) + 4096 * a (m + 1) := a_rec (m + 1)
  have h2 : a (m + 6) = -4 * a (m + 5) + 256 * a (m + 3) + 4096 * a (m + 2) := a_rec (m + 2)
  linarith [h0, h1, h2]

/-- The squares of `c` satisfy the same "step by two" recurrence that the odd-indexed
subsequence of `a` satisfies. -/
theorem c_id (k : ℕ) :
    c (k + 3) ^ 2 = -48 * c (k + 2) ^ 2 + 3072 * c (k + 1) ^ 2 + 262144 * c k ^ 2 := by
  have e2 : c (k + 2) = -4 * c (k + 1) - 64 * c k := c_rec k
  have e3 : c (k + 3) = -4 * c (k + 2) - 64 * c (k + 1) := c_rec (k + 1)
  rw [e3, e2]
  ring

/-- The key identity, proved by induction with a three-term sliding window:
`a (2*k+1) = (c k)²` for all `k`. -/
theorem oeis_113254_key : ∀ k : ℕ,
    a (2 * k + 1) = c k ^ 2 ∧ a (2 * k + 3) = c (k + 1) ^ 2 ∧ a (2 * k + 5) = c (k + 2) ^ 2 := by
  intro k
  induction k with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> rfl
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · have hidx : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
      rw [hidx]; exact ih2
    · have hidx : 2 * (k + 1) + 3 = 2 * k + 5 := by ring
      rw [hidx]; exact ih3
    · have hidx : 2 * (k + 1) + 5 = 2 * k + 1 + 6 := by ring
      rw [hidx, a_step2 (2 * k + 1)]
      have i4 : 2 * k + 1 + 4 = 2 * k + 5 := by ring
      have i2 : 2 * k + 1 + 2 = 2 * k + 3 := by ring
      rw [i4, i2, ih1, ih2, ih3]
      linarith [c_id k]

theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  refine ⟨c n, ?_⟩
  have h := (oeis_113254_key n).1
  rw [h]; ring
