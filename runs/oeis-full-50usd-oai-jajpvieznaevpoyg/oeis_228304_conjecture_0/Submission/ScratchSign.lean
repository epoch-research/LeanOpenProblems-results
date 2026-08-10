import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators

example (n : ℕ) : (Fin.revPerm (n:=n)).sign = ∏ j : Fin n, ∏ i ∈ Finset.Iio j, (-1 : ℤˣ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i < j := by simpa using hi
  have hnot : ¬ Fin.rev i < Fin.rev j := by
    exact not_lt.mpr (Fin.rev_le_rev.mpr (le_of_lt hij))
  simp [Fin.revPerm, hnot]

example (n : ℕ) : (∏ j : Fin n, ∏ i ∈ Finset.Iio j, (-1 : ℤˣ)) = (-1 : ℤˣ) ^ (n * (n-1) / 2) := by
  calc
    (∏ j : Fin n, ∏ i ∈ Finset.Iio j, (-1 : ℤˣ)) = ∏ j : Fin n, (-1 : ℤˣ) ^ (j : ℕ) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.prod_const]
      simp [Nat.card_Iio]
    _ = (-1 : ℤˣ) ^ (∑ j : Fin n, (j : ℕ)) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (-1 : ℤˣ) ^ (n * (n-1) / 2) := by
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
      exact Finset.sum_range_id n

