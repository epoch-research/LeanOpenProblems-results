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

def u (n : ℕ) : ℤ :=
  match n with
  | 0 => -2
  | 1 => -56
  | n' + 2 => -4 * u (n' + 1) - 64 * u n'

theorem u_recurrence (n : ℕ) : u (n + 3) ^ 2 = -48 * u (n + 2) ^ 2 + 3072 * u (n + 1) ^ 2 + 262144 * u n ^ 2 := by
  have h1 : u (n + 3) = -4 * u (n + 2) - 64 * u (n + 1) := rfl
  have h2 : u (n + 2) = -4 * u (n + 1) - 64 * u n := rfl
  rw [h1, h2]
  ring

theorem a_recurrence (n : ℕ) : a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  have h1 : a (n + 6) = -4 * a (n + 5) + 256 * a (n + 3) + 4096 * a (n + 2) := rfl
  have h2 : a (n + 5) = -4 * a (n + 4) + 256 * a (n + 2) + 4096 * a (n + 1) := rfl
  have h3 : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := rfl
  rw [h1, h2, h3]
  ring

theorem a_eq_u_sq (n : ℕ) : a (2 * n + 1) = u n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · rfl
    · rfl
    · rfl
    · have h_a : a (2 * (k + 3) + 1) = a ((2 * k + 1) + 6) := rfl
      rw [h_a]
      rw [a_recurrence (2 * k + 1)]
      have ih0 : a (2 * k + 1) = u k ^ 2 := ih k (by omega)
      have ih1 : a (2 * (k + 1) + 1) = u (k + 1) ^ 2 := ih (k + 1) (by omega)
      have ih2 : a (2 * (k + 2) + 1) = u (k + 2) ^ 2 := ih (k + 2) (by omega)
      have h_idx1 : (2 * k + 1) + 2 = 2 * (k + 1) + 1 := rfl
      have h_idx2 : (2 * k + 1) + 4 = 2 * (k + 2) + 1 := rfl
      rw [h_idx1, h_idx2]
      rw [ih2, ih1, ih0]
      rw [← u_recurrence k]

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [isSquare_iff_exists_sq]
  use u n
  exact a_eq_u_sq n
