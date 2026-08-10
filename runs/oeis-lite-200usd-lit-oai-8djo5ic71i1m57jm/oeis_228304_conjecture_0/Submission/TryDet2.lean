import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

#check Matrix.det_permute_column
#check Matrix.det_of_upperTriangular
#check Matrix.BlockTriangular
#check Matrix.det_of_lowerTriangular
#check Fin.rev_add_cast
#check Fin.add_rev_cast
#check Equiv.Perm.sign_eq_prod_prod_Iio

lemma test_tri (p : ℕ) (s : ℕ → ZMod p) (hzero : ∀ n, p ≤ n → s n = 0) :
    (Matrix.of fun i j : Fin p => s (i.val + (Fin.revPerm j).val)).BlockTriangular id := by
  intro i j hij
  simp only [Matrix.of_apply]
  apply hzero
  -- BlockTriangular id means ?
  sorry
