import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_padicValNat_le (p M n : ℕ) (hp : p.Prime)
  (h_R : n * (n + 1) / 2 = p * M + p * p - 2 * p)
  (h_L : n * (n + 1) / 2 - n = p * M)
  (hM : p ≤ M) :
  ∑ x ∈ Icc (p * M + 1) (p * M + p * p - 2 * p), padicValNat p x ≤ p - 2 := by
  sorry
