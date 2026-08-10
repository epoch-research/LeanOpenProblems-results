import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def S_a08 (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m }

lemma mem_S_a08_imp_abundant {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ S_a08 n) :
  2 * m ≤ (Nat.divisors m).sum id := by sorry

lemma mem_S_a08_imp_card_divisors {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ S_a08 n) :
  n < (Nat.divisors m).card := by sorry

lemma no_smaller_candidate_a08_ge_13_except : ∀ m < 180, m ≠ 120 ∧ m ≠ 144 ∧ m ≠ 168 → ∀ k ≥ 13, m ∉ S_a08 k := by
  intro m hm h_neq k hk h_mem
  have h_ab : 2 * m ≤ (Nat.divisors m).sum id := mem_S_a08_imp_abundant (by omega) h_mem
  have h_cd : k < (Nat.divisors m).card := mem_S_a08_imp_card_divisors (by omega) h_mem
  have h_poss : (Nat.divisors m).card < 14 ∨ (Nat.divisors m).sum id < 2 * m := by
    have h_dec : ∀ x < 180, x ≠ 120 ∧ x ≠ 144 ∧ x ≠ 168 → (Nat.divisors x).card < 14 ∨ (Nat.divisors x).sum id < 2 * x := by decide
    exact h_dec m hm h_neq
  rcases h_poss with hc1 | hc2
  · omega
  · omega
