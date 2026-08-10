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
def u (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => -2
  | n' + 2 => -4 * u (n' + 1) - 64 * u n'

lemma u_succ_succ (n : ℕ) : u (n + 2) = -4 * u (n + 1) - 64 * u n := rfl

def w (n : ℕ) : ℤ := u (n + 1) ^ 2
def z (n : ℕ) : ℤ := u (n + 2) * u (n + 1)

lemma z_succ (n : ℕ) : z (n + 1) = -4 * w (n + 1) - 64 * z n := by
  dsimp [z, w]
  rw [u_succ_succ (n + 1)]
  ring

lemma w_succ (n : ℕ) : w (n + 2) = 16 * w (n + 1) + 512 * z n + 4096 * w n := by
  dsimp [z, w]
  rw [u_succ_succ (n + 1)]
  ring

lemma w_recurrence (n : ℕ) : w (n + 3) = -48 * w (n + 2) + 3072 * w (n + 1) + 262144 * w n := by
  have h1 := w_succ (n + 1)
  have h2 := z_succ n
  have h3 := w_succ n
  linear_combination h1 + 512 * h2 + 64 * h3

lemma a_succ_four (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := rfl

lemma a_recurrence_step (n : ℕ) : a (2 * n + 7) = -48 * a (2 * n + 5) + 3072 * a (2 * n + 3) + 262144 * a (2 * n + 1) := by
  have h1 : a (2 * n + 7) = -4 * a (2 * n + 6) + 256 * a (2 * n + 4) + 4096 * a (2 * n + 3) := a_succ_four (2 * n + 3)
  have h2 : a (2 * n + 6) = -4 * a (2 * n + 5) + 256 * a (2 * n + 3) + 4096 * a (2 * n + 2) := a_succ_four (2 * n + 2)
  have h3 : a (2 * n + 5) = -4 * a (2 * n + 4) + 256 * a (2 * n + 2) + 4096 * a (2 * n + 1) := a_succ_four (2 * n + 1)
  linear_combination h1 - 4 * h2 + 64 * h3

theorem a_eq_w (n : ℕ) : a (2 * n + 1) = w n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · have ih1 := ih (k + 2) (by omega)
    have ih2 := ih (k + 1) (by omega)
    have ih3 := ih k (by omega)
    have ha := a_recurrence_step k
    have hw := w_recurrence k
    have h_idx1 : 2 * (k + 3) + 1 = 2 * k + 7 := by omega
    have h_idx2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have h_idx3 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h_idx4 : 2 * k + 1 = 2 * k + 1 := by omega
    rw [h_idx1, ha]
    rw [h_idx2] at ih1
    rw [h_idx3] at ih2
    rw [h_idx4] at ih3
    rw [ih1, ih2, ih3]
    exact hw.symm

theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  use u (n + 1)
  rw [a_eq_w n]
  dsimp [w]
  ring
