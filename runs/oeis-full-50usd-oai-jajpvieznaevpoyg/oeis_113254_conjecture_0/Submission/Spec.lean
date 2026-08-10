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
def x (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => -2
  | n' + 2 => -4 * x (n' + 1) - 64 * x n'

lemma x_sq_rec (n : ℕ) :
    x (n + 4) ^ 2 =
      -48 * x (n + 3) ^ 2 + 3072 * x (n + 2) ^ 2 + 262144 * x (n + 1) ^ 2 := by
  simp [x]
  ring

lemma a_six_rec (n : ℕ) :
    a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  simp [a]
  ring

lemma a_odd_rec (n : ℕ) :
    a (2 * (n + 3) + 1) =
      -48 * a (2 * (n + 2) + 1) +
        3072 * a (2 * (n + 1) + 1) + 262144 * a (2 * n + 1) := by
  simpa only [Nat.mul_add, Nat.reduceMul, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using a_six_rec (2 * n + 1)

lemma a_odd_eq_x_sq : ∀ n : ℕ, a (2 * n + 1) = x (n + 1) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num [a, x]
      | 1 => norm_num [a, x]
      | 2 => norm_num [a, x]
      | m + 3 =>
          rw [a_odd_rec m, x_sq_rec m]
          rw [ih m (by omega), ih (m + 1) (by omega), ih (m + 2) (by omega)]

theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  refine ⟨x (n + 1), ?_⟩
  simpa [pow_two] using a_odd_eq_x_sq n
