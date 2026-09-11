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

def u : ℕ → ℤ
| 0 => 0
| 1 => 32
| (n + 2) => 64 * u n

def v : ℕ → ℤ
| 0 => -1
| 1 => -28
| (n + 2) => -4 * v (n + 1) - 64 * v n

lemma a_eq : ∀ n, a n = u n + v n
| 0 => rfl
| 1 => rfl
| 2 => rfl
| 3 => rfl
| (n + 4) => by
  have ha : a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n := rfl
  rw [ha]
  rw [a_eq (n + 3), a_eq (n + 1), a_eq n]
  have hu : u (n + 4) = -4 * u (n + 3) + 256 * u (n + 1) + 4096 * u n := by
    calc u (n + 4) = 64 * u (n + 2) := rfl
      _ = 64 * (64 * u n) := rfl
      _ = 4096 * u n := by ring
      _ = -4 * (64 * u (n + 1)) + 256 * u (n + 1) + 4096 * u n := by ring
      _ = -4 * u (n + 3) + 256 * u (n + 1) + 4096 * u n := rfl
  have hv : v (n + 4) = -4 * v (n + 3) + 256 * v (n + 1) + 4096 * v n := by
    calc v (n + 4) = -4 * v (n + 3) - 64 * v (n + 2) := rfl
      _ = -4 * v (n + 3) - 64 * (-4 * v (n + 1) - 64 * v n) := rfl
      _ = -4 * v (n + 3) + 256 * v (n + 1) + 4096 * v n := by ring
  rw [hu, hv]
  ring

lemma u_odd : ∀ n, u (2 * n + 1) = 32 * 64 ^ n
| 0 => rfl
| (n + 1) => by
  have eq1 : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
  rw [eq1]
  change 64 * u (2 * n + 1) = 32 * 64 ^ (n + 1)
  rw [u_odd n]
  have h64 : (64 : ℤ) ^ (n + 1) = 64 ^ n * 64 := by rw [pow_add, pow_one]
  rw [h64]
  ring

def w : ℕ → ℤ
| 0 => 2
| 1 => -4
| (n + 2) => -4 * w (n + 1) - 64 * w n

lemma w_mul : ∀ (m k : ℕ), w (k + 2 * m) + 64^m * w k = w (k + m) * w m
| 0, k => by
  change w k + 1 * w k = w k * 2
  ring
| 1, k => by
  change w (k + 2) + 64 * w k = w (k + 1) * (-4)
  have : w (k + 2) = -4 * w (k + 1) - 64 * w k := rfl
  linarith
| (m + 2), k => by
  have h1 := w_mul (m + 1) (k + 1)
  have h2 := w_mul m (k + 2)
  have h1_sub : w (k + 2 * m + 3) + 64 ^ (m + 1) * w (k + 1) = w (k + m + 2) * w (m + 1) := by
    have eq1 : k + 2 * m + 3 = k + 1 + 2 * (m + 1) := by omega
    have eq2 : k + m + 2 = k + 1 + (m + 1) := by omega
    rw [eq1, eq2]; exact h1
  have h2_sub : w (k + 2 * m + 2) + 64 ^ m * w (k + 2) = w (k + m + 2) * w m := by
    have eq1 : k + 2 * m + 2 = k + 2 + 2 * m := by omega
    have eq2 : k + m + 2 = k + 2 + m := by omega
    rw [eq1, eq2]; exact h2
  calc w (k + 2 * (m + 2)) + 64 ^ (m + 2) * w k 
    _ = w (k + 2 * m + 4) + 64 ^ (m + 2) * w k := by 
      have eq : k + 2 * (m + 2) = k + 2 * m + 4 := by omega
      rw [eq]
    _ = -4 * w (k + 2 * m + 3) - 64 * w (k + 2 * m + 2) + 64 ^ (m + 2) * w k := by 
      have : w (k + 2 * m + 4) = -4 * w (k + 2 * m + 3) - 64 * w (k + 2 * m + 2) := rfl
      rw [this]
    _ = -4 * (w (k + m + 2) * w (m + 1) - 64 ^ (m + 1) * w (k + 1)) 
        - 64 * (w (k + m + 2) * w m - 64 ^ m * w (k + 2)) + 64 ^ (m + 2) * w k := by
      have : w (k + 2 * m + 3) = w (k + m + 2) * w (m + 1) - 64 ^ (m + 1) * w (k + 1) := by linarith [h1_sub]
      rw [this]
      have : w (k + 2 * m + 2) = w (k + m + 2) * w m - 64 ^ m * w (k + 2) := by linarith [h2_sub]
      rw [this]
    _ = w (k + m + 2) * (-4 * w (m + 1) - 64 * w m) 
        + 64 ^ (m + 1) * (4 * w (k + 1) + w (k + 2)) + 64 ^ (m + 2) * w k := by ring
    _ = w (k + m + 2) * w (m + 2) 
        + 64 ^ (m + 1) * (4 * w (k + 1) + w (k + 2)) + 64 ^ (m + 2) * w k := by 
      have hw : w (m + 2) = -4 * w (m + 1) - 64 * w m := rfl
      rw [hw]
    _ = w (k + m + 2) * w (m + 2) 
        + 64 ^ (m + 1) * (-64 * w k) + 64 ^ (m + 2) * w k := by
      have hwk : w (k + 2) = -4 * w (k + 1) - 64 * w k := rfl
      have : 4 * w (k + 1) + w (k + 2) = -64 * w k := by linarith [hwk]
      rw [this]
    _ = w (k + m + 2) * w (m + 2) := by ring
    _ = w (k + (m + 2)) * w (m + 2) := by
      have eq : k + m + 2 = k + (m + 2) := by omega
      rw [eq]

lemma w_eq_4v : ∀ n, w (n + 1) = 4 * v n
| 0 => rfl
| 1 => rfl
| (n + 2) => by
  calc w (n + 3) = -4 * w (n + 2) - 64 * w (n + 1) := rfl
    _ = -4 * (4 * v (n + 1)) - 64 * (4 * v n) := by rw [w_eq_4v (n+1), w_eq_4v n]
    _ = 4 * (-4 * v (n + 1) - 64 * v n) := by ring
    _ = 4 * v (n + 2) := rfl

lemma v_eq : ∀ n, v (2 * n + 1) = 4 * v n ^ 2 - 32 * 64 ^ n := by
  intro n
  have hw := w_mul (n + 1) 0
  have eq1 : 0 + 2 * (n + 1) = 2 * n + 2 := by omega
  have eq2 : 0 + (n + 1) = n + 1 := by omega
  rw [eq1, eq2] at hw
  have hw_val : w 0 = 2 := rfl
  rw [hw_val] at hw
  have h1 : w (2 * n + 2) = 4 * v (2 * n + 1) := w_eq_4v (2 * n + 1)
  have h2 : w (n + 1) = 4 * v n := w_eq_4v n
  rw [h1, h2] at hw
  have h64 : (64 : ℤ) ^ (n + 1) = 64 ^ n * 64 := by rw [pow_add, pow_one]
  rw [h64] at hw
  linarith

theorem a_odd_square : ∀ n : ℕ, a (2 * n + 1) = (2 * v n) ^ 2 := by
  intro n
  rw [a_eq]
  rw [u_odd]
  rw [v_eq]
  ring

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  use 2 * v n
  rw [a_odd_square]
  ring

theorem oeis_113254_conjecture_0.disproof : ¬ (type_of% @oeis_113254_conjecture_0) := sorry
