import FormalConjectures.Util.ProblemImports

open Nat
open Matrix Complex
open scoped BigOperators

def a (n : ℕ) : ℕ := 4 ^ n * n.factorial ^ 2

open Equiv Fintype Finset in
theorem perm_succ_column_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    A.permanent = ∑ i : Fin n.succ, A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
  rw [Matrix.permanent, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.permanent, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, of_apply, Equiv.swap_self,
      Equiv.refl_apply]
  · simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ, ← Fin.succAbove_cycleRange]
    rw [Matrix.permanent, Finset.mul_sum]
    simp only [of_apply]
    rw [← (Group.mulLeft_bijective (i.cycleRange)).sum_comp
          (fun τ : Equiv.Perm (Fin n) => A i.succ 0 * ∏ j, A (i.succ.succAbove (τ j)) j.succ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Equiv.Perm.mul_apply]

-- Step 1: reduce the entry to (ζ^j + ζ^k)/(ζ^k - ζ^j).
example (n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 * n + 1)) :
    True := by
  -- explore
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  trivial

-- Test reduction of the actual goal structure
theorem reduce_goal (n : ℕ) :
  let N : ℕ := 2 * n
  let K : ℕ := N + 1
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
  (
    let M : Matrix (Fin N) (Fin N) ℂ := of fun j k : Fin N =>
      if j = k then 1
      else
        let pow : ℤ := (j : ℤ) - (k : ℤ)
        (1 + ζ ^ pow) / (1 - ζ ^ pow)
    M.permanent = (a n : ℂ) / (K : ℂ)
  ) := by
  intro N K ζ hζ
  simp only
  sorry
