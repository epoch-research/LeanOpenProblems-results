import FormalConjectures.Util.ProblemImports

open Nat Finset

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

example : prod_factor_plus 5 1 = 670442572800 := by
  unfold prod_factor_plus product_indices
  norm_num
