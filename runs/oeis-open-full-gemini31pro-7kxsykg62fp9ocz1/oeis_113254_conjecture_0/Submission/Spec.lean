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
| 0 => 1
| 1 => -2
| n + 2 => -4 * u (n + 1) - 64 * u n

def y : ℕ → ℤ
| 0 => -1
| 1 => -28
| n + 2 => -4 * y (n + 1) - 64 * y n

def b (n : ℕ) : ℤ := 2 * 8 ^ n - 2 * (-8 : ℤ) ^ n + y n

lemma y_rec4 (n : ℕ) : y (n + 4) = -4 * y (n + 3) + 256 * y (n + 1) + 4096 * y n := by
  calc
    y (n + 4) = -4 * y (n + 3) - 64 * y (n + 2) := rfl
    _ = -4 * y (n + 3) - 64 * (-4 * y (n + 1) - 64 * y n) := rfl
    _ = -4 * y (n + 3) + 256 * y (n + 1) + 4096 * y n := by ring

lemma b_rec (n : ℕ) : b (n + 4) = -4 * b (n + 3) + 256 * b (n + 1) + 4096 * b n := by
  dsimp [b]
  have hy := y_rec4 n
  have h8_1 : (8 : ℤ) ^ (n + 1) = (8 : ℤ) ^ n * 8 := by
    calc
      (8 : ℤ) ^ (n + 1) = (8 : ℤ) ^ n * (8 : ℤ) ^ 1 := pow_add 8 n 1
      _ = (8 : ℤ) ^ n * 8 := by ring
  have h8_3 : (8 : ℤ) ^ (n + 3) = (8 : ℤ) ^ n * 512 := by
    calc
      (8 : ℤ) ^ (n + 3) = (8 : ℤ) ^ n * (8 : ℤ) ^ 3 := pow_add 8 n 3
      _ = (8 : ℤ) ^ n * 512 := by ring
  have h8_4 : (8 : ℤ) ^ (n + 4) = (8 : ℤ) ^ n * 4096 := by
    calc
      (8 : ℤ) ^ (n + 4) = (8 : ℤ) ^ n * (8 : ℤ) ^ 4 := pow_add 8 n 4
      _ = (8 : ℤ) ^ n * 4096 := by ring
  have hn8_1 : (-8 : ℤ) ^ (n + 1) = (-8 : ℤ) ^ n * (-8) := by
    calc
      (-8 : ℤ) ^ (n + 1) = (-8 : ℤ) ^ n * (-8 : ℤ) ^ 1 := pow_add (-8) n 1
      _ = (-8 : ℤ) ^ n * (-8) := by ring
  have hn8_3 : (-8 : ℤ) ^ (n + 3) = (-8 : ℤ) ^ n * (-512) := by
    calc
      (-8 : ℤ) ^ (n + 3) = (-8 : ℤ) ^ n * (-8 : ℤ) ^ 3 := pow_add (-8) n 3
      _ = (-8 : ℤ) ^ n * (-512) := by ring
  have hn8_4 : (-8 : ℤ) ^ (n + 4) = (-8 : ℤ) ^ n * 4096 := by
    calc
      (-8 : ℤ) ^ (n + 4) = (-8 : ℤ) ^ n * (-8 : ℤ) ^ 4 := pow_add (-8) n 4
      _ = (-8 : ℤ) ^ n * 4096 := by ring
  rw [h8_1, h8_3, h8_4, hn8_1, hn8_3, hn8_4, hy]
  ring

lemma a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | n' + 4 =>
      have h1 : a (n' + 4) = -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n' := rfl
      rw [h1]
      have ih3 := ih (n' + 3) (by omega)
      have ih1 := ih (n' + 1) (by omega)
      have ih0 := ih n' (by omega)
      rw [ih3, ih1, ih0]
      exact (b_rec n').symm

lemma u_inv (n : ℕ) : u (n + 1) ^ 2 + 4 * u n * u (n + 1) + 64 * u n ^ 2 = 60 * 64 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      u (n + 2) ^ 2 + 4 * u (n + 1) * u (n + 2) + 64 * u (n + 1) ^ 2
      _ = (-4 * u (n + 1) - 64 * u n) ^ 2 + 4 * u (n + 1) * (-4 * u (n + 1) - 64 * u n) + 64 * u (n + 1) ^ 2 := by rw [u]
      _ = 64 * (u (n + 1) ^ 2 + 4 * u n * u (n + 1) + 64 * u n ^ 2) := by ring
      _ = 64 * (60 * 64 ^ n) := by rw [ih]
      _ = 60 * 64 ^ (n + 1) := by ring

lemma y_eq (n : ℕ) : y (2 * n) = u n * u (n + 1) + 64 ^ n ∧ y (2 * n + 1) = u (n + 1) ^ 2 - 32 * 64 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    have hy2n2 : y (2 * n + 2) = u (n + 1) * u (n + 2) + 64 ^ (n + 1) := by
      calc
        y (2 * n + 2) = -4 * y (2 * n + 1) - 64 * y (2 * n) := rfl
        _ = -4 * (u (n + 1) ^ 2 - 32 * 64 ^ n) - 64 * (u n * u (n + 1) + 64 ^ n) := by rw [ih1, ih2]
        _ = u (n + 1) * (-4 * u (n + 1) - 64 * u n) + 64 * 64 ^ n := by ring
        _ = u (n + 1) * u (n + 2) + 64 ^ (n + 1) := by
          have h : u (n + 2) = -4 * u (n + 1) - 64 * u n := rfl
          rw [h]
          ring
    constructor
    · have h : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [h]
      exact hy2n2
    · have h : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
      rw [h]
      calc
        y (2 * n + 3) = -4 * y (2 * n + 2) - 64 * y (2 * n + 1) := rfl
        _ = -4 * (u (n + 1) * u (n + 2) + 64 ^ (n + 1)) - 64 * (u (n + 1) ^ 2 - 32 * 64 ^ n) := by rw [hy2n2, ih2]
        _ = -4 * u (n + 1) * u (n + 2) - 64 * u (n + 1) ^ 2 + 28 * 64 ^ (n + 1) := by ring
        _ = (-4 * u (n + 1) * u (n + 2) - 64 * u (n + 1) ^ 2 + 60 * 64 ^ (n + 1)) - 32 * 64 ^ (n + 1) := by ring
        _ = (-4 * u (n + 1) * u (n + 2) - 64 * u (n + 1) ^ 2 + (u (n + 2) ^ 2 + 4 * u (n + 1) * u (n + 2) + 64 * u (n + 1) ^ 2)) - 32 * 64 ^ (n + 1) := by rw [u_inv (n + 1)]
        _ = u (n + 2) ^ 2 - 32 * 64 ^ (n + 1) := by ring

lemma pow_diff (n : ℕ) : 2 * (8 : ℤ) ^ (2 * n + 1) - 2 * (-8 : ℤ) ^ (2 * n + 1) = 32 * 64 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      2 * (8 : ℤ) ^ (2 * (n + 1) + 1) - 2 * (-8 : ℤ) ^ (2 * (n + 1) + 1)
      _ = 2 * (8 : ℤ) ^ (2 * n + 1 + 2) - 2 * (-8 : ℤ) ^ (2 * n + 1 + 2) := by
        have h1 : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
        rw [h1]
      _ = 2 * ((8 : ℤ) ^ (2 * n + 1) * 64) - 2 * ((-8 : ℤ) ^ (2 * n + 1) * 64) := by
        have h8 : (8 : ℤ) ^ (2 * n + 1 + 2) = (8 : ℤ) ^ (2 * n + 1) * 64 := by
          calc (8 : ℤ) ^ (2 * n + 1 + 2) = (8 : ℤ) ^ (2 * n + 1) * (8 : ℤ) ^ 2 := pow_add 8 (2 * n + 1) 2
               _ = (8 : ℤ) ^ (2 * n + 1) * 64 := by ring
        have hn8 : (-8 : ℤ) ^ (2 * n + 1 + 2) = (-8 : ℤ) ^ (2 * n + 1) * 64 := by
          calc (-8 : ℤ) ^ (2 * n + 1 + 2) = (-8 : ℤ) ^ (2 * n + 1) * (-8 : ℤ) ^ 2 := pow_add (-8) (2 * n + 1) 2
               _ = (-8 : ℤ) ^ (2 * n + 1) * 64 := by ring
        rw [h8, hn8]
      _ = 64 * (2 * (8 : ℤ) ^ (2 * n + 1) - 2 * (-8 : ℤ) ^ (2 * n + 1)) := by ring
      _ = 64 * (32 * 64 ^ n) := by rw [ih]
      _ = 32 * 64 ^ (n + 1) := by ring

lemma a_odd_square (n : ℕ) : a (2 * n + 1) = u (n + 1) * u (n + 1) := by
  calc
    a (2 * n + 1) = b (2 * n + 1) := a_eq_b (2 * n + 1)
    _ = 2 * (8 : ℤ) ^ (2 * n + 1) - 2 * (-8 : ℤ) ^ (2 * n + 1) + y (2 * n + 1) := rfl
    _ = 32 * 64 ^ n + y (2 * n + 1) := by rw [pow_diff]
    _ = 32 * 64 ^ n + (u (n + 1) ^ 2 - 32 * 64 ^ n) := by rw [(y_eq n).2]
    _ = u (n + 1) * u (n + 1) := by ring

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  use u (n + 1)
  exact a_odd_square n

theorem oeis_113254_conjecture_0.disproof : ¬ (type_of% @oeis_113254_conjecture_0) := sorry
