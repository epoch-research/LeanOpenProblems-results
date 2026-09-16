import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma p_dvd_prod_x (p M : ℕ) (hp5 : 5 ≤ p) (hM : p ≤ M) (hp_dvd : p ∣ M - 1) :
  p ∣ ∏ x ∈ Icc (M - p + 3) M, x := by
  apply dvd_prod_of_mem
  rw [mem_Icc]
  constructor
  · zify [show p ≤ M by omega]
    omega
  · omega
