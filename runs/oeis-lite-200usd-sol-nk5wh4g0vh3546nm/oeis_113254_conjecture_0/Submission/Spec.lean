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

def b (n : ℕ) : ℤ :=
  match n with
  | 0 => 2
  | 1 => 56
  | n + 2 => -4 * b (n + 1) - 64 * b n

lemma a_sameParity (n : ℕ) :
    a (n + 6) = -48 * a (n + 4) + 3072 * a (n + 2) + 262144 * a n := by
  simp only [a]
  ring

lemma b_square_recurrence (n : ℕ) :
    b (n + 3) ^ 2 =
      -48 * b (n + 2) ^ 2 + 3072 * b (n + 1) ^ 2 + 262144 * b n ^ 2 := by
  simp only [b]
  ring

lemma threeStepInduction {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (step : ∀ n, P n → P (n + 1) → P (n + 2) → P (n + 3)) : ∀ n, P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · exact h0
      rcases n with _ | n
      · exact h1
      rcases n with _ | n
      · exact h2
      exact step n (ih n (by omega)) (ih (n + 1) (by omega)) (ih (n + 2) (by omega))


lemma a_odd_eq_b_square : ∀ n : ℕ, a (2 * n + 1) = b n ^ 2 := by
  apply threeStepInduction
  · norm_num [a, b]
  · norm_num [a, b]
  · norm_num [a, b]
  · intro n h0 h1 h2
    rw [show 2 * (n + 3) + 1 = (2 * n + 1) + 6 by omega, a_sameParity]
    rw [show (2 * n + 1) + 4 = 2 * (n + 2) + 1 by omega,
        show (2 * n + 1) + 2 = 2 * (n + 1) + 1 by omega,
        h2, h1, h0, b_square_recurrence]

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [a_odd_eq_b_square]
  exact ⟨b n, by simp [pow_two]⟩
