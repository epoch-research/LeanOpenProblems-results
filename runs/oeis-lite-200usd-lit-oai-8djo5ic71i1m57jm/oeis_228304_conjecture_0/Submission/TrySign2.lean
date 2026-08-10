import FormalConjectures.Util.ProblemImports
open Nat Finset Matrix

lemma sign_revPerm_units (n : ℕ) :
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

lemma sign_revPerm_int_odd (p m : ℕ) (hp : p = 2*m + 1) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ℤˣ) : ℤ) = (-1 : ℤ) ^ m := by
  subst p
  rw [sign_revPerm_units]
  have hexp : (2 * m + 1) * (2 * m + 1 - 1) / 2 = m * (2*m+1) := by
    rw [show 2 * m + 1 - 1 = 2*m by omega]
    rw [show (2*m+1) * (2*m) = 2 * (m * (2*m+1)) by ring]
    rw [Nat.mul_div_right _ (by norm_num : 0 < 2)]
  rw [hexp]
  have hpow_units : (-1 : ℤˣ) ^ (m * (2*m+1)) = (-1 : ℤˣ) ^ m := by
    apply neg_one_pow_congr
    rw [Nat.even_mul]
    have hodd : Odd (2*m+1) := ⟨m, rfl⟩
    constructor
    · intro h
      exact h.resolve_right ((Nat.not_even_iff_odd).2 hodd)
    · intro hm
      exact Or.inl hm
  rw [hpow_units]
  simp
