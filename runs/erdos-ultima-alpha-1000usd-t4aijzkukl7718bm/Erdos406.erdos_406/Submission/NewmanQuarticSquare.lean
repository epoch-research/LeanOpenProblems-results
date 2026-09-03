import Submission.NewmanQuotientCertificate

/-! The known quartic factor of the digit polynomial of 256 is squarefree
in every normalized Newman polynomial. This does not classify the other
possible factors and does not settle Erdős 406. -/
namespace Erdos406QuarticSquare
open Polynomial Erdos406Quotient
noncomputable def qQuartic : ℤ[X] := X ^ 4 - X ^ 3 + X ^ 2 + 1

lemma qQuartic_sq_expanded : qQuartic ^ 2 =
    1 + 2 * X ^ 2 - 2 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 +
      3 * X ^ 6 - 2 * X ^ 7 + X ^ 8 := by
  unfold qQuartic
  ring

lemma qQuartic_sq_list : qQuartic ^ 2 = listPoly [1, 0, 2, -2, 3, -2, 3, -2, 1] := by
  simp [qQuartic, listPoly]
  ring
def sSquare : List ℤ := [-92, -154, 299, -91, -342, 494, -25, -693, 767, 197, -1315, 1097, 738, -2341, 1390, 1879, -3915, 1408, 4027, -6098, 673, 7681, -8696, -1601, 13188, -10947, -6370, 20081, -11142, -13955, 25592, -6538, -21479, 21806, 5154, -16273, -8878, 19229, 39130, 32145, 3915, -24153, -33538, -21210, 1262, 18227, 20782, 10766, -2920, -11420, -11186, -4681, 2670, 6451, 5525, 1765, -1884, -3400, -2562, -545, 1164, 1701, 1126, 102, -660, -817, -471, 28, 353, 379, 186, -48, -180, -170, -69, 37, 89, 74, 23]
def eSquare : List ℤ := [-92, -154, 115, -215, 288, -564, 402, -170, -2, 2, -3, 3, -4, 5, -5, 6, -5, 5, -4, 3, -2, 1, -2, 0, -1, 0, 0, -1, 1, 0, 0, 1, -1, 1, 0, -1, 1, -2, 1, 0, 0, -1, 0, -1, 1, -2, 3, -2, 3, -2, 2, 0, 0, 2, -1, 2, -2, 2, -1, 0, 1, -1, 1, -2, 2, -1, 1, -2, 1, 1, -1, 1, -2, 2, -1, 0, 0, -1, 2, 21, 44, 77, 45, 35, 10, 28, 23]

lemma qQuartic_sq_certificate :
    listPoly sSquare * qQuartic ^ 2 = monomial 39 131070 + listPoly eSquare := by
  rw [qQuartic_sq_list]
  apply listPoly_certificate
  decide +kernel

lemma qQuartic_sq_quotient_bound (P R : ℤ[X]) (hPR : P = qQuartic ^ 2 * R)
    (hP : ∀ i, |P.coeff i| ≤ 1) : ∀ i, |R.coeff i| ≤ 3 := by
  intro i
  have hh := quotient_bound (qQuartic ^ 2) P R sSquare eSquare 131070 39
    hPR qQuartic_sq_certificate hP i
  norm_num [weight, sSquare, eSquare] at hh
  omega

set_option maxHeartbeats 2000000 in
/-- No normalized Newman polynomial has the square of the known quartic
as a divisor, regardless of its degree. -/
theorem qQuartic_sq_not_dvd_newman (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) : ¬ qQuartic ^ 2 ∣ P := by
  rintro ⟨R, hPR⟩
  have hb := qQuartic_sq_quotient_bound P R hPR (fun i => by
    rcases hP i with h | h <;> rw [h] <;> norm_num)
  have hr0 : R.coeff 0 = 1 := by simpa [hPR, coeff_zero_eq_eval_zero, qQuartic] using h0
  have h2 : P.coeff 2 ≤ 1 := by rcases hP 2 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h2
  have h5 : P.coeff 5 ≤ 1 := by rcases hP 5 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h5
  have h8 : P.coeff 8 ≤ 1 := by rcases hP 8 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h8
  have h11 : P.coeff 11 ≤ 1 := by rcases hP 11 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h11
  have h15 : -P.coeff 3 ≤ 0 := by rcases hP 3 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h15
  have h16 : -P.coeff 4 ≤ 0 := by rcases hP 4 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h16
  have h18 : -P.coeff 6 ≤ 0 := by rcases hP 6 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h18
  have h19 : -P.coeff 7 ≤ 0 := by rcases hP 7 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h19
  have h21 : -P.coeff 9 ≤ 0 := by rcases hP 9 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h21
  have h22 : -P.coeff 10 ≤ 0 := by rcases hP 10 with h | h <;> omega
  norm_num [hPR, qQuartic_sq_expanded, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h22
  have h34 : R.coeff 10 ≤ 3 := (abs_le.mp (hb 10)).2
  have h47 : -R.coeff 11 ≤ 3 := by have hh := (abs_le.mp (hb 11)).1; omega
  have hc : 176 * R.coeff 0 ≤ 173 := by
    linear_combination 96 * h2 + 40 * h5 + 14 * h8 + 2 * h11 + 62 * h15 + 13 * h16 + 17 * h18 + 8 * h19 + 4 * h21 + 5 * h22 + 5 * h34 + 2 * h47
  omega

theorem qQuartic_sq_not_dvd_digits (w : List ℕ) (hw : w ⊆ [0, 1]) :
    ¬ qQuartic ^ 2 ∣ Nat.ofDigits (X : ℤ[X]) (1 :: w) := by
  apply qQuartic_sq_not_dvd_newman
  · simp [Nat.ofDigits]
  · exact ofDigits_coeff_zero_one _ (by simpa using hw)

/-- The quartic can occur at most once in any normalized Newman polynomial. -/
theorem qQuartic_multiplicity_bound (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) (m : ℕ)
    (hd : qQuartic ^ m ∣ P) : m ≤ 1 := by
  by_contra hh
  exact qQuartic_sq_not_dvd_newman P h0 hP
    ((pow_dvd_pow qQuartic (by omega : 2 ≤ m)).trans hd)

/-- Conditional classification: if the only factors are X+1 and the known
quartic, the three known polynomials exhaust the possibilities. The
factorization premise is not asserted for arbitrary candidates. -/
theorem known_factor_family (P : ℤ[X])
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) (r s : ℕ)
    (he : P = (X + 1) ^ r * qQuartic ^ s) :
    P = 1 ∨ P = X + 1 ∨ P = (X + 1) * qQuartic := by
  have h0 : P.coeff 0 = 1 := by
    simp [he, coeff_zero_eq_eval_zero, qQuartic]
  have hs : s ≤ 1 := qQuartic_multiplicity_bound P h0 hP s (by
    rw [he]
    exact dvd_mul_left _ _)
  have hc : P.coeff 1 = (r : ℤ) := by
    rw [he]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · simp [coeff_X_add_one_pow]
    · rw [pow_one, mul_comm]
      simp [qQuartic, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul',
        coeff_X_add_one_pow]
  have hr : r ≤ 1 := by
    have hp := hP 1
    rw [hc] at hp
    rcases hp with hp | hp <;> exact_mod_cast (by omega : (r : ℤ) ≤ 1)
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;>
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · exact Or.inl (by simpa using he)
  · have hp := hP 3
    norm_num [he, qQuartic, coeff_one] at hp
  · exact Or.inr (Or.inl (by simpa using he))
  · exact Or.inr (Or.inr (by simpa using he))

#print axioms known_factor_family
#print axioms qQuartic_multiplicity_bound
#print axioms qQuartic_sq_quotient_bound
#print axioms qQuartic_sq_not_dvd_newman
#print axioms qQuartic_sq_not_dvd_digits
end Erdos406QuarticSquare
