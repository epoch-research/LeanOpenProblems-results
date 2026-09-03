import Submission.PrimeSupport

/-!
Two-adic arithmetic of the finite normalized Lambert pole product.
This is an auxiliary restriction on factorial clearing, not a proof or
disproof of Erdős 68.
-/
namespace PoleProductArithmetic
open Erdos68Development

noncomputable def productValue (N : ℕ) : ℚ :=
  ∏ k ∈ Finset.range N, (1 - 1/((k+2).factorial : ℚ))

def numerator (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, denom k
def denominator (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, (k+2).factorial
def countTwos (N : ℕ) : ℕ := ∑ k ∈ Finset.range N, (k+2)/2

lemma denominator_pos (N : ℕ) : 0 < denominator N := by
  apply Finset.prod_pos
  intro k hk
  exact Nat.factorial_pos _

lemma value_eq (N : ℕ) :
    productValue N = (numerator N : ℚ)/(denominator N : ℚ) := by
  unfold productValue numerator denominator
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hd : (denom k : ℚ) = ((k+2).factorial : ℚ)-1 := by
    unfold denom
    rw [Nat.cast_sub (Nat.factorial_pos _)]
    norm_num
  rw [hd]
  have hf : ((k+2).factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma numerator_coprime_two (N : ℕ) : Nat.Coprime 2 (numerator N) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro k hk
  exact Nat.prime_two.coprime_iff_not_dvd.mpr
    (prime_not_dvd_denom_of_le Nat.prime_two (by omega))

lemma factorial_twos (n : ℕ) : 2^(n/2) ∣ n.factorial := by
  have h : n/2 ≤ padicValNat 2 n.factorial := by
    have he := padicValNat_factorial_mul (p := 2) (n/2)
    rw [padicValNat_mul_div_factorial] at he
    omega
  exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mpr h

lemma twos_dvd_denominator (N : ℕ) : 2^(countTwos N) ∣ denominator N := by
  induction N with
  | zero => simp [countTwos, denominator]
  | succ N ih =>
    simp only [countTwos, denominator, Finset.sum_range_succ, Finset.prod_range_succ,
      pow_add] at *
    exact Nat.mul_dvd_mul ih (factorial_twos (N+2))

/-- Clearing the rational product's value requires all these powers of two,
even if its numerator and denominator have first been reduced. -/
theorem twos_dvd_any_clearing (N C : ℕ) (z : ℤ)
    (h : (C:ℚ)*productValue N = z) : 2^(countTwos N) ∣ C := by
  rw [value_eq] at h
  have hd0 : (denominator N : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos N).ne'
  have hid : (C:ℤ)*(numerator N : ℤ) = z*(denominator N : ℤ) := by
    apply Rat.intCast_injective
    push_cast
    exact (div_eq_iff hd0).mp (by simpa only [mul_div_assoc] using h)
  have hd : (2:ℤ)^(countTwos N) ∣ (denominator N : ℤ) := by
    exact_mod_cast twos_dvd_denominator N
  have ht : (2:ℤ)^(countTwos N) ∣ (numerator N : ℤ)*C := by
    rw [mul_comm, hid]
    exact dvd_mul_of_dvd_right hd _
  have hc : IsCoprime ((2:ℤ)^(countTwos N)) (numerator N : ℤ) := by
    exact_mod_cast ((numerator_coprime_two N).pow_left (countTwos N)).isCoprime
  exact_mod_cast hc.dvd_of_dvd_mul_left ht

theorem twos_dvd_reduced_den (N : ℕ) :
    2^(countTwos N) ∣ (productValue N).den := by
  exact twos_dvd_any_clearing N (productValue N).den (productValue N).num
    (Rat.den_mul_eq_num _)

lemma quadratic_count (N : ℕ) : N^2 ≤ 4*countTwos N := by
  induction N with
  | zero => simp [countTwos]
  | succ N ih =>
    have hs : countTwos (N+1) = countTwos N + (N+2)/2 := by
      simp [countTwos, Finset.sum_range_succ]
    have hd : 2*N+1 ≤ 4*((N+2)/2) := by omega
    rw [hs]
    nlinarith

/-- For N cancelled rows, any positive factorial index clearing the product
value must exceed the two-adic count. -/
theorem factorial_clearing_index (N M : ℕ) (hM : 0 < M) (z : ℤ)
    (h : (M.factorial : ℚ)*productValue N = z) : countTwos N < M := by
  have hd := twos_dvd_any_clearing N M.factorial z h
  have hl := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero M)).mp hd
  exact hl.trans_lt (padicValNat_factorial_lt_of_ne_zero 2 (Nat.ne_of_gt hM))

/-- A quadratic necessary bound, valid after arbitrary rational reduction
of the product value. No analytic error bound is asserted here. -/
theorem quadratic_factorial_clearing (N M : ℕ) (hM : 0 < M) (z : ℤ)
    (h : (M.factorial : ℚ)*productValue N = z) : N^2 < 4*M := by
  have hh := factorial_clearing_index N M hM z h
  have hq := quadratic_count N
  omega

end PoleProductArithmetic

#print axioms PoleProductArithmetic.twos_dvd_reduced_den
#print axioms PoleProductArithmetic.factorial_clearing_index
#print axioms PoleProductArithmetic.quadratic_factorial_clearing
