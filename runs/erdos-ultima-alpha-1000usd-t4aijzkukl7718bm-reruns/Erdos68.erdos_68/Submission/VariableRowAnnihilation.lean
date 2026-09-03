import FormalConjecturesUtil

/-!
An arithmetic constraint on arbitrary finite, integer-weighted annihilation
of a geometric Lambert row. This is auxiliary work, not a solution of Spec.
-/

namespace VariableRowAnnihilation

private lemma clear_term (a z : ℤ) (e M : ℕ) (ha : a ≠ 0) (he : e ≤ M) :
    ((z : ℚ) / (a : ℚ) ^ e) * (a : ℚ) ^ M =
      (z : ℚ) * (a : ℚ) ^ (M - e) := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hp : (a : ℚ) ^ M = (a : ℚ) ^ e * (a : ℚ) ^ (M - e) := by
    rw [← pow_add, Nat.add_sub_of_le he]
  rw [hp]
  field_simp

/-- The weights and exponents need not come from a constant-coefficient
operator, or even from consecutive indices. -/
theorem denominator_dvd_weight_sum {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (e : ι → ℕ) (a : ℤ) (ha : a ≠ 0)
    (hzero : ∑ i ∈ s, (z i : ℚ) / (a : ℚ) ^ e i = 0) :
    a - 1 ∣ ∑ i ∈ s, z i := by
  classical
  let M := s.sup e
  have hb : ∀ i ∈ s, e i ≤ M := fun i hi => Finset.le_sup hi
  have hQ : ∑ i ∈ s, (z i : ℚ) * (a : ℚ) ^ (M - e i) = 0 := by
    calc
      _ = (∑ i ∈ s, (z i : ℚ) / (a : ℚ) ^ e i) * (a : ℚ) ^ M := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        exact (clear_term a (z i) (e i) M ha (hb i hi)).symm
      _ = 0 := by rw [hzero, zero_mul]
  have hZ : ∑ i ∈ s, z i * a ^ (M - e i) = 0 := by exact_mod_cast hQ
  have hd : a - 1 ∣ ∑ i ∈ s, z i * (a ^ (M - e i) - 1) := by
    apply Finset.dvd_sum
    intro i hi
    apply dvd_mul_of_dvd_right
    simpa only [one_pow] using sub_dvd_pow_sub_pow a 1 (M - e i)
  have heq : (∑ i ∈ s, z i * (a ^ (M - e i) - 1)) = -(∑ i ∈ s, z i) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hZ, zero_sub]
  rwa [heq, dvd_neg] at hd

/-- In particular such an annihilator cannot retain coefficient one on a
constant sequence when the base is at least three. -/
theorem no_unit_weight_sum {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (e : ι → ℕ) (a : ℤ) (ha : 3 ≤ a)
    (hzero : ∑ i ∈ s, (z i : ℚ) / (a : ℚ) ^ e i = 0) :
    ∑ i ∈ s, z i ≠ 1 := by
  intro h
  have hd := denominator_dvd_weight_sum s z e a (by omega) hzero
  rw [h] at hd
  have hl := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hd
  omega

/-- Application to a Lambert row at arbitrary selected indices. The common
factor `d! - 1` in the row denominator does not change its annihilators. -/
theorem factorial_row_denominator_dvd {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (index : ι → ℕ) (d : ℕ) (hd : 2 ≤ d)
    (hzero : ∑ i ∈ s, (z i : ℚ) /
      (((d.factorial : ℚ) ^ (index i / d)) * (d.factorial - 1)) = 0) :
    (d.factorial : ℤ) - 1 ∣ ∑ i ∈ s, z i := by
  have hf : 1 < d.factorial := Nat.one_lt_factorial.mpr (by omega)
  have hfQ : (1 : ℚ) < d.factorial := by exact_mod_cast hf
  have hne : (d.factorial : ℚ) - 1 ≠ 0 := by linarith
  have hdiv : (∑ i ∈ s, (z i : ℚ) /
      ((d.factorial : ℚ) ^ (index i / d))) / (d.factorial - 1) = 0 := by
    simpa only [Finset.sum_div, div_div] using hzero
  have hb : ∑ i ∈ s, (z i : ℚ) / ((d.factorial : ℚ) ^ (index i / d)) = 0 :=
    (div_eq_zero_iff.mp hdiv).resolve_right hne
  have h := denominator_dvd_weight_sum s z (fun i => index i / d)
    (d.factorial : ℤ) (by positivity) (by simpa only [Int.cast_natCast] using hb)
  exact h

end VariableRowAnnihilation

#print axioms VariableRowAnnihilation.denominator_dvd_weight_sum
#print axioms VariableRowAnnihilation.no_unit_weight_sum
#print axioms VariableRowAnnihilation.factorial_row_denominator_dvd
