import FormalConjectures.Util.ProblemImports
open Nat Finset

def GB_set (m : ℕ) : Finset ℕ :=
  if m = 0 then ∅ else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime

  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧
    r < p ∧
    p ≤ m / 2 ∧
    (∀ q ∈ small_primes, p % q ≠ m % q)

  (Finset.range (m / 2 + 1)).filter is_gb_associated

theorem part1 (m : ℕ) (h : m ≥ 6) (p : ℕ) (hp : p ∈ GB_set m) : Nat.Prime (m - p) := by
  sorry
