import FormalConjectures.Util.ProblemImports
open Nat

theorem prime_bound_step (y : ℕ) (hy : 1 ≤ y) :
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  p (y + 1) ≤ 2 * p y := by
  intro p
  dsimp [p]
  have h_inf : {x : ℕ | Nat.Prime x}.Infinite := Nat.infinite_setOf_prime
  have hPy_pos : p y ≠ 0 := by
    dsimp [p]
    have : 2 ≤ nth Nat.Prime y := by
      calc 2 ≤ nth Nat.Prime 1 := by rw [nth_prime_one_eq_three]; decide
      _ ≤ nth Nat.Prime y := (nth_strictMono h_inf).monotone hy
    omega
  rcases Nat.exists_prime_lt_and_le_two_mul (nth Nat.Prime y) hPy_pos with ⟨q, hq_prime, h_lt, h_le⟩
  have h_le_succ : nth Nat.Prime (y + 1) ≤ q := by
    by_contra h_gt
    push_neg at h_gt
    have h_le_y := Nat.le_nth_of_lt_nth_succ h_gt hq_prime
    omega
  omega
