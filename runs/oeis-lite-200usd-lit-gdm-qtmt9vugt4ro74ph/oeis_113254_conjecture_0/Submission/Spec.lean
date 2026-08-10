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
def b : ℕ → ℤ
  | 0 => -2
  | 1 => 56
  | n + 2 => 4 * b (n + 1) - 64 * b n

lemma b_rec (n : ℕ) : b (n + 3) * b (n + 3) = -48 * (b (n + 2) * b (n + 2)) + 3072 * (b (n + 1) * b (n + 1)) + 262144 * (b n * b n) := by
  have hb3 : b (n + 3) = 4 * b (n + 2) - 64 * b (n + 1) := rfl
  have hb2 : b (n + 2) = 4 * b (n + 1) - 64 * b n := rfl
  rw [hb3, hb2]
  ring

lemma a_rec (k : ℕ) : a (k + 6) = -48 * a (k + 4) + 3072 * a (k + 2) + 262144 * a k := by
  have h4 : a (k + 4) = -4 * a (k + 3) + 256 * a (k + 1) + 4096 * a k := rfl
  have h5 : a (k + 5) = -4 * a (k + 4) + 256 * a (k + 2) + 4096 * a (k + 1) := rfl
  have h6 : a (k + 6) = -4 * a (k + 5) + 256 * a (k + 3) + 4096 * a (k + 2) := rfl
  rw [h6, h5, h4]
  ring

lemma a_eq_b_sq (n : ℕ) : a (2 * n + 1) = b n * b n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · have h_idx : 2 * (m + 3) + 1 = (2 * m + 1) + 6 := by omega
    rw [h_idx]
    rw [a_rec (2 * m + 1)]
    have h_idx4 : 2 * m + 1 + 4 = 2 * (m + 2) + 1 := by omega
    have h_idx2 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
    rw [h_idx4, h_idx2]
    have ih2 : a (2 * (m + 2) + 1) = b (m + 2) * b (m + 2) := ih (m + 2) (by omega)
    have ih1 : a (2 * (m + 1) + 1) = b (m + 1) * b (m + 1) := ih (m + 1) (by omega)
    have ih0 : a (2 * m + 1) = b m * b m := ih m (by omega)
    rw [ih2, ih1, ih0]
    rw [← b_rec m]

theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  use b n
  exact a_eq_b_sq n
