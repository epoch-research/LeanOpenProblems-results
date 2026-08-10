import FormalConjectures.Util.ProblemImports
open Nat Finset Matrix

example (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp only [Fin.revPerm_apply]
  have hinner : ∀ x : Fin n, (∏ y ∈ Iio x, if x < y then (1 : ℤˣ) else -1) = ∏ _y ∈ Iio x, (-1 : ℤˣ) := by
    intro x
    apply Finset.prod_congr rfl
    intro y hy
    rw [if_neg]
    exact not_lt_of_gt (by simpa using hy)
  simp [hinner, Fin.card_Iio, Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [show (∑ i : Fin n, (i : ℕ)) = ∑ i ∈ range n, i by
    simpa using (Fin.sum_univ_eq_sum_range (fun x => x) n)]
  rw [Finset.sum_range_id]
