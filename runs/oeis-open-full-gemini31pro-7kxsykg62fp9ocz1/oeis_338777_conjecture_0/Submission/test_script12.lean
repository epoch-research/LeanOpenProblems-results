import FormalConjectures.Util.ProblemImports
open Nat Finset

def A338777 (n : ℕ) : ℕ :=
  let m := 2 * n
  if m = 0 then 1 else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime
  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧ r < p ∧ p ≤ m / 2 ∧ (∀ q ∈ small_primes, p % q ≠ m % q)
  let GB_2n : Finset ℕ := (Finset.range (m / 2 + 1)).filter is_gb_associated
  GB_2n.prod id

def GB_set (m : ℕ) : Finset ℕ :=
  if m = 0 then ∅ else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime
  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧ r < p ∧ p ≤ m / 2 ∧ (∀ q ∈ small_primes, p % q ≠ m % q)
  (Finset.range (m / 2 + 1)).filter is_gb_associated

lemma A338777_eq_prod (n : ℕ) (hn : n > 0) : A338777 n = (GB_set (2 * n)).prod id := by
  dsimp [A338777, GB_set]
  have hm : 2 * n ≠ 0 := by omega
  rw [if_neg hm, if_neg hm]
