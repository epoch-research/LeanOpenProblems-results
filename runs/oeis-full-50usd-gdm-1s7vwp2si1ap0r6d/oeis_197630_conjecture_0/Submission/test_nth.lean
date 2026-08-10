import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Prime.Nth

theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 13) = 13 := Nat.nth_count (by decide : (13 : ℕ).Prime)
  have hc : Nat.count Nat.Prime 13 = 5 := by rfl
  rw [hc] at h
  exact h

