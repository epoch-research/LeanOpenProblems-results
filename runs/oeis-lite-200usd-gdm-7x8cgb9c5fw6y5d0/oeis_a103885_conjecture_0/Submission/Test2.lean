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
  have h1 : (∏ k ∈ Finset.Ioc (0 : ℕ) (2 * 5 : ℕ), (2 * ↑(5 : ℕ) * ↑(1 : ℕ) + (k : ℝ))) = ∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), ((k + 10 : ℕ) : ℝ) := by
    have h_dom : Finset.Ioc (0 : ℕ) (2 * 5 : ℕ) = Finset.Ioc (0 : ℕ) (10 : ℕ) := by norm_num
    rw [h_dom]
    refine Finset.prod_congr rfl (fun x hx => ?_)
    push_cast
    ring
  rw [h1, ← Finset.prod_natCast]
  have h2 : (∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), (k + 10)) = 670442572800 := by decide
  rw [h2]
  rfl

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

example : prod_factor_minus 5 1 = 0 := by
  unfold prod_factor_minus product_indices
  have h1 : (∏ k ∈ Finset.Ioc (0 : ℕ) (2 * 5 : ℕ), (2 * ↑(5 : ℕ) * ↑(1 : ℕ) - (k : ℝ))) = ∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), (((10 - k : ℕ) : ℝ)) := by
    have h_dom : Finset.Ioc (0 : ℕ) (2 * 5 : ℕ) = Finset.Ioc (0 : ℕ) (10 : ℕ) := by norm_num
    rw [h_dom]
    refine Finset.prod_congr rfl (fun x hx => ?_)
    have hx_le : x ≤ 10 := by
      have h_mem := Finset.mem_Ioc.mp hx
      omega
    rw [Nat.cast_sub hx_le]
    push_cast
    ring
  rw [h1, ← Finset.prod_natCast]
  have h2 : (∏ k ∈ Finset.Ioc (0 : ℕ) (10 : ℕ), (10 - k)) = 0 := by decide
  rw [h2]
  push_cast
  rfl
