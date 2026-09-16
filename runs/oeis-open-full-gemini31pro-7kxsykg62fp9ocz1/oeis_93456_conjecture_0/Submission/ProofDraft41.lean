import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma p_dvd_prod_x (p M : ℕ) (hp5 : 5 ≤ p) (hM : p ≤ M) (hp_dvd : p ∣ M - 1) :
  p ∣ ∏ x ∈ Icc (M - p + 3) M, x := by
  have H : M - 1 ∈ Icc (M - p + 3) M := by
    rw [mem_Icc]
    constructor
    · omega
    · omega
  exact dvd_trans hp_dvd (dvd_prod_of_mem (fun x => x) H)
