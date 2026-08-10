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
def r : ℕ → ℤ
  | 0 => -2
  | 1 => -56
  | n + 2 => -4 * r (n + 1) - 64 * r n

lemma a_step2 (n : ℕ) :
    a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  rw [show n + 6 = (n + 2) + 4 by omega]
  simp [a]
  ring

lemma r_sq_step (n : ℕ) :
    (r (n + 3)) ^ 2 =
      -48 * (r (n + 2)) ^ 2 + 3072 * (r (n + 1)) ^ 2 + 262144 * (r n) ^ 2 := by
  rw [show n + 3 = (n + 1) + 2 by omega]
  rw [show n + 2 = n + 2 by rfl]
  simp [r]
  ring

lemma a_odd_eq_r_sq : ∀ n : ℕ, a (2 * n + 1) = (r n) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num [a, r]
      | 1 => norm_num [a, r]
      | 2 => norm_num [a, r]
      | n + 3 =>
          have ha := a_step2 (2 * n + 1)
          have hr := r_sq_step n
          have h0 : a (2 * n + 1) = (r n) ^ 2 := ih n (by omega)
          have h1 : a (2 * (n + 1) + 1) = (r (n + 1)) ^ 2 := ih (n + 1) (by omega)
          have h2 : a (2 * (n + 2) + 1) = (r (n + 2)) ^ 2 := ih (n + 2) (by omega)
          rw [show 2 * (n + 3) + 1 = (2 * n + 1) + 6 by omega]
          rw [ha]
          rw [show (2 * n + 1) + 4 = 2 * (n + 2) + 1 by omega]
          rw [show (2 * n + 1) + 2 = 2 * (n + 1) + 1 by omega]
          rw [h0, h1, h2]
          exact hr.symm

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [a_odd_eq_r_sq n]
  exact ⟨r n, by ring⟩
