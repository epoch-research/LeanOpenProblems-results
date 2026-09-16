import Submission.Factorial
import Mathlib

open Nat

def D (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * (n:ℤ)) - (2 * (k:ℤ) + 1)) |>.prod

lemma D_zero (n : ℕ) : D n 0 = 1 := rfl

lemma D_succ (n r : ℕ) : D n (r + 1) = D n r * (8 * (n:ℤ) - (2 * (r:ℤ) + 1)) := by
  dsimp [D]
  rw [List.range_succ, List.map_append, List.prod_append]
  dsimp
  ring

lemma identity_Z (n r : ℕ) (hr : r ≤ 4 * n) :
    D n r * (2 ^ r : ℤ) * ((4 * n).descFactorial r : ℤ) = ((8 * n).descFactorial (2 * r) : ℤ) := by
  induction r with
  | zero =>
    simp [D_zero]
  | succ r ih =>
    have hr' : r ≤ 4 * n := by omega
    have ih' := ih hr'
    rw [D_succ]
    have h1 : (2 ^ (r + 1) : ℤ) = (2 ^ r : ℤ) * 2 := by ring
    have h2 : ((4 * n).descFactorial (r + 1) : ℤ) = ((4 * n).descFactorial r : ℤ) * (4 * (n:ℤ) - (r:ℤ)) := by
      have e1 : (4 * n).descFactorial (r + 1) = (4 * n).descFactorial r * (4 * n - r) := by
        rw [Nat.descFactorial_succ, mul_comm]
      rw [e1]
      push_cast
      have e2 : ((4 * n - r : ℕ) : ℤ) = 4 * (n:ℤ) - (r:ℤ) := by omega
      rw [e2]
    
    have h3 : ((8 * n).descFactorial (2 * (r + 1)) : ℤ) = ((8 * n).descFactorial (2 * r) : ℤ) * (8 * (n:ℤ) - 2 * (r:ℤ)) * (8 * (n:ℤ) - 2 * (r:ℤ) - 1) := by
      have e1 : 2 * (r + 1) = 2 * r + 2 := by ring
      rw [e1]
      have e2 : (8 * n).descFactorial (2 * r + 2) = (8 * n).descFactorial (2 * r) * (8 * n - 2 * r) * (8 * n - (2 * r + 1)) := by
        have e_succ1 : (8 * n).descFactorial (2 * r + 2) = (8 * n).descFactorial (2 * r + 1) * (8 * n - (2 * r + 1)) := by
          have := @Nat.descFactorial_succ (8 * n) (2 * r + 1)
          rw [this, mul_comm]
        have e_succ2 : (8 * n).descFactorial (2 * r + 1) = (8 * n).descFactorial (2 * r) * (8 * n - 2 * r) := by
          have := @Nat.descFactorial_succ (8 * n) (2 * r)
          rw [this, mul_comm]
        rw [e_succ1, e_succ2, mul_assoc]
      rw [e2]
      push_cast
      have e4 : ((8 * n - 2 * r : ℕ) : ℤ) = 8 * (n:ℤ) - 2 * (r:ℤ) := by omega
      have e5 : ((8 * n - (2 * r + 1) : ℕ) : ℤ) = 8 * (n:ℤ) - 2 * (r:ℤ) - 1 := by omega
      rw [e4, e5]

    rw [h1, h2, h3]
    calc D n r * (8 * ↑n - (2 * ↑r + 1)) * (2 ^ r * 2) * (↑((4 * n).descFactorial r) * (4 * ↑n - ↑r))
      = (D n r * 2 ^ r * ↑((4 * n).descFactorial r)) * (8 * ↑n - (2 * ↑r + 1)) * 2 * (4 * ↑n - ↑r) := by ring
    _ = (↑((8 * n).descFactorial (2 * r))) * (8 * ↑n - (2 * ↑r + 1)) * 2 * (4 * ↑n - ↑r) := by rw [ih']
    _ = ↑((8 * n).descFactorial (2 * r)) * (8 * ↑n - 2 * ↑r) * (8 * ↑n - 2 * ↑r - 1) := by ring

