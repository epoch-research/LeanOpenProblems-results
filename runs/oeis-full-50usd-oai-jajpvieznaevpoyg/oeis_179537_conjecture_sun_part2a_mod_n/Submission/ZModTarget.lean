import FormalConjectures.Util.ProblemImports
open Finset Nat Int

def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

example (n : ℕ) (hn : n ≥ 1) : A179537_sum_weighted n ≡ 0 [ZMOD n] := by
  rw [Int.modEq_zero_iff_dvd]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [A179537_sum_weighted, A179537, Int.cast_sum, map_sum, Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_natCast]
  -- show target
  try simp
