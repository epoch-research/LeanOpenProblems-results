import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

lemma sign_revPerm_units (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp [Fin.revPerm_apply, Fin.card_Iio]
  sorry

lemma sign_revPerm_int_odd (p m : ℕ) (hp : p = 2*m + 1) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin p)) : ℤˣ) : ℤ) = (-1 : ℤ) ^ m := by
  rw [sign_revPerm_units]
  rw [show p * (p - 1) / 2 = m * (2*m+1) by omega]
  rw [show (-1 : ℤˣ) ^ (m * (2*m+1)) = ((-1 : ℤˣ) ^ m) by
    -- parity
    rw [← pow_mul]
    have hodd : ((-1 : ℤˣ) ^ (2*m+1)) = -1 := by simp [pow_succ, pow_mul]
    rw [hodd]
  ]
  simp
