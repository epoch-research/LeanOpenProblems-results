import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Prime.Nth

open BigOperators Nat Int

def fermat_quotient_int (k p : ℕ) : ℤ := (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))

def wilson_quotient_int (p : ℕ) : ℤ := ((p - 1).factorial + 1) / (p : ℤ)

noncomputable def a (n : ℕ) : ℕ :=
  if 1 < n then
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let p_z : ℤ := p_n
    let sum_q : ℤ := Finset.sum (Finset.range (p_n - 1)) (fun k : ℕ => fermat_quotient_int (k + 1) p_n)
    let L_p : ℤ := sum_q - wilson_quotient_int p_n
    (L_p / p_z).natAbs
  else
    0

theorem nth_prime_seven_eq_nineteen_local : Nat.nth Nat.Prime 7 = 19 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 19) = 19 := Nat.nth_count (by decide : (19 : ℕ).Prime)
  have hc : Nat.count Nat.Prime 19 = 7 := by rfl
  rw [hc] at h
  exact h

example : a 8 = 166710337513971577670 := by
  unfold a
  dsimp
  rw [nth_prime_seven_eq_nineteen_local]
  decide
