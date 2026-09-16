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

lemma gb_prop (m : ℕ) (p : ℕ) (hp : p ∈ GB_set m) :
    m ≠ 0 ∧ Nat.Prime p ∧ Nat.sqrt m < p ∧ p ≤ m / 2 ∧
    ∀ q, Nat.Prime q → q ≤ Nat.sqrt m → p % q ≠ m % q := by
  dsimp [GB_set] at hp
  split_ifs at hp with h0
  · simp at hp
  · rw [mem_filter, mem_range] at hp
    rcases hp with ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h0, h2, h3, h4, fun q hq hq2 => ?_⟩
    apply h5
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le hq2, hq⟩
