import FormalConjectures.Util.ProblemImports
open PowerSeries

lemma coeff_pow_eq_coeff_trunc_pow {m a : ℕ} (f : PowerSeries ℤ) :
    PowerSeries.coeff m (f^a) = PowerSeries.coeff m (((PowerSeries.trunc (m+1) f : Polynomial ℤ) : PowerSeries ℤ)^a) := by
  rw [← PowerSeries.coeff_coe_trunc_of_lt (f := f^a) (n := m) (m := m+1) (Nat.lt_succ_self m)]
  rw [← PowerSeries.coeff_coe_trunc_of_lt (f := (((PowerSeries.trunc (m+1) f : Polynomial ℤ) : PowerSeries ℤ)^a)) (n := m) (m := m+1) (Nat.lt_succ_self m)]
  congr 1
  exact congr_arg (fun p : Polynomial ℤ => (p : PowerSeries ℤ)) (PowerSeries.trunc_trunc_pow f (m+1) a).symm

lemma coeff_eq_of_trunc_eq_pow8_fast {m : ℕ} {f g : PowerSeries ℤ}
    (h : PowerSeries.trunc (m+1) f = PowerSeries.trunc (m+1) g) :
    PowerSeries.coeff m (f^8) = PowerSeries.coeff m (g^8) := by
  rw [coeff_pow_eq_coeff_trunc_pow (m := m) (a := 8) f]
  rw [coeff_pow_eq_coeff_trunc_pow (m := m) (a := 8) g]
  rw [h]
