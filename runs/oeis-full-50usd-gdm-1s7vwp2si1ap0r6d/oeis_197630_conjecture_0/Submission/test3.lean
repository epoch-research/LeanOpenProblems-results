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

example : a 3 = 13 := by
  unfold a
  dsimp
  rw [nth_prime_two_eq_five]
  decide
