import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma prod_px (p M : ℕ) (hp5 : 5 ≤ p) (hM : p ≤ M) :
  (∏ x ∈ Icc (M - p + 3) M, (p * x)) = p^(p - 2) * ∏ x ∈ Icc (M - p + 3) M, x := by
  rw [prod_mul_distrib, prod_const]
  congr 1
  have : (Icc (M - p + 3) M).card = p - 2 := by
    rw [Nat.card_Icc]
    zify [show p ≤ M by omega]
    omega
  rw [this]
