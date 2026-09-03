import Submission.NewmanQuotientCertificate

/-! Exclusion of one particular degree-ten polynomial. This does not classify
 all possible higher-degree factors or settle Erdős 406. -/
namespace Erdos406Quotient
open Polynomial
noncomputable def qTen : ℤ[X] := 1 - X + X ^ 2 - X ^ 4 + X ^ 8 + X ^ 10
def sTen : List ℤ := [0, 0, -2, -3, -2, -3, -2, -3, -3, -2, 0, 2, 3, 5, 6, 9, 11, 13, 10, 6, 4, 4, 0, -11, -24, -31, -27, -26, -37, -51, -46, -13, 20, 24, 10, 29, 104, 176, 164, 82, 47, 130, 217, 117, -167, -359, -243, -25, -161, -706, -1052, -617, 224, 377, -490, -1101, 17, 2226, 2932, 929, -1158, 379, 4735, 6009, 589, -6166, -4969, 4050, 7834, -3690, -3687, -2334, 3863, 2664, -505, -3387, -1884, 3807, 1039, -131, -3230, 378, 1289, 1503, -627, -2171, 590, 588, 1563, -1444, -477, -326, 1051, 601, -890, -234, -446, 1246, -284, 6, -730, 235, 520, -77, 9, -690, 551, -88, 384, -458, -82, 130, 68, 246, -463, 199, -205, 388, -172, -33, -52, -7, 268, -202, 145, -247, 253, -59, 58, -91, -113, 129, -114, 115, -282, 38, -104, 122, 0, -122, 0]
def eTen : List ℤ := [0, 0, -2, -1, -1, -4, 1, -1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1, 1, 0, 0, 1, 0, 0, 1, -1, 1, 0, 0, 1, -1, 1, 0, -1, 1, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, -1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, -1, 0, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -2, 1, -1, -1, 1, -1, 0, 0, 0, 1, -1, 1, 0, -1, 0, -396, 275, -386, 160, -104, 0, 0, -122, 0]

lemma qTen_list : qTen = listPoly [1, -1, 1, 0, -1, 0, 0, 0, 1, 0, 1] := by
  simp [qTen, listPoly]
  ring

lemma qTen_certificate :
    listPoly sTen * qTen = monomial 70 16383 + listPoly eTen := by
  rw [qTen_list]
  apply listPoly_certificate
  decide +kernel

lemma qTen_quotient_bound (P R : ℤ[X]) (hPR : P = qTen * R)
    (hP : ∀ i, |P.coeff i| ≤ 1) : ∀ i, |R.coeff i| ≤ 6 := by
  intro i
  have hh := quotient_bound qTen P R sTen eTen 16383 70 hPR qTen_certificate hP i
  norm_num [weight, sTen, eTen] at hh
  omega

set_option maxHeartbeats 8000000 in
theorem qTen_not_dvd_newman (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) : ¬ qTen ∣ P := by
  rintro ⟨R, hPR⟩
  have hb := qTen_quotient_bound P R hPR (fun i => by
    rcases hP i with h | h <;> rw [h] <;> norm_num)
  have hh (i : ℕ) : -6 ≤ R.coeff i ∧ R.coeff i ≤ 6 := abs_le.mp (hb i)
  have hr0 : R.coeff 0 = 1 := by
    simpa [hPR, qTen] using h0
  have h7 : P.coeff 7 ≤ 1 := by rcases hP 7 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h7
  have h8 : P.coeff 8 ≤ 1 := by rcases hP 8 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h8
  have h11 : P.coeff 11 ≤ 1 := by rcases hP 11 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h11
  have h12 : P.coeff 12 ≤ 1 := by rcases hP 12 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h12
  have h13 : P.coeff 13 ≤ 1 := by rcases hP 13 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h13
  have h14 : P.coeff 14 ≤ 1 := by rcases hP 14 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h14
  have h15 : P.coeff 15 ≤ 1 := by rcases hP 15 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h15
  have h16 : P.coeff 16 ≤ 1 := by rcases hP 16 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h16
  have h17 : P.coeff 17 ≤ 1 := by rcases hP 17 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h17
  have h18 : P.coeff 18 ≤ 1 := by rcases hP 18 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h18
  have h19 : P.coeff 19 ≤ 1 := by rcases hP 19 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h19
  have h32 : P.coeff 32 ≤ 1 := by rcases hP 32 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h32
  have h33 : P.coeff 33 ≤ 1 := by rcases hP 33 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h33
  have h34 : P.coeff 34 ≤ 1 := by rcases hP 34 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h34
  have h35 : P.coeff 35 ≤ 1 := by rcases hP 35 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h35
  have h36 : P.coeff 36 ≤ 1 := by rcases hP 36 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h36
  have h37 : P.coeff 37 ≤ 1 := by rcases hP 37 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h37
  have h38 : P.coeff 38 ≤ 1 := by rcases hP 38 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h38
  have h39 : P.coeff 39 ≤ 1 := by rcases hP 39 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h39
  have h40 : P.coeff 40 ≤ 1 := by rcases hP 40 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h40
  have h44 : P.coeff 44 ≤ 1 := by rcases hP 44 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h44
  have h49 : 0 ≤ P.coeff 1 := by rcases hP 1 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h49
  have h52 : 0 ≤ P.coeff 4 := by rcases hP 4 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h52
  have h53 : 0 ≤ P.coeff 5 := by rcases hP 5 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h53
  have h54 : 0 ≤ P.coeff 6 := by rcases hP 6 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h54
  have h58 : 0 ≤ P.coeff 10 := by rcases hP 10 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h58
  have h68 : 0 ≤ P.coeff 20 := by rcases hP 20 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h68
  have h69 : 0 ≤ P.coeff 21 := by rcases hP 21 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h69
  have h70 : 0 ≤ P.coeff 22 := by rcases hP 22 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h70
  have h71 : 0 ≤ P.coeff 23 := by rcases hP 23 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h71
  have h72 : 0 ≤ P.coeff 24 := by rcases hP 24 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h72
  have h73 : 0 ≤ P.coeff 25 := by rcases hP 25 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h73
  have h74 : 0 ≤ P.coeff 26 := by rcases hP 26 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h74
  have h75 : 0 ≤ P.coeff 27 := by rcases hP 27 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h75
  have h76 : 0 ≤ P.coeff 28 := by rcases hP 28 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h76
  have h77 : 0 ≤ P.coeff 29 := by rcases hP 29 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h77
  have h78 : 0 ≤ P.coeff 30 := by rcases hP 30 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h78
  have h79 : 0 ≤ P.coeff 31 := by rcases hP 31 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h79
  have h89 : 0 ≤ P.coeff 41 := by rcases hP 41 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h89
  have h90 : 0 ≤ P.coeff 42 := by rcases hP 42 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h90
  have h93 : 0 ≤ P.coeff 45 := by rcases hP 45 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h93
  have h94 : 0 ≤ P.coeff 46 := by rcases hP 46 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h94
  have h95 : 0 ≤ P.coeff 47 := by rcases hP 47 with h | h <;> omega
  norm_num [hPR, qTen, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at h95
  have b1 := (hh 1).1
  have b2 := (hh 2).1
  have b5 := (hh 5).1
  have b6 := (hh 6).2
  have b12 := (hh 12).1
  have b16 := (hh 16).2
  have b18 := (hh 18).2
  have b20 := (hh 20).1
  have b23 := (hh 23).1
  have b24 := (hh 24).2
  have b26 := (hh 26).1
  have b29 := (hh 29).1
  have b30 := (hh 30).2
  have b32 := (hh 32).2
  have b41 := (hh 41).1
  have b42 := (hh 42).1
  have b45 := (hh 45).2
  have b47 := (hh 47).2
  linarith only [hr0, h7, h8, h11, h12, h13, h14, h15, h16, h17, h18, h19, h32, h33, h34, h35, h36, h37, h38, h39, h40, h44, h49, h52, h53, h54, h58, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h89, h90, h93, h94, h95, b1, b2, b5, b6, b12, b16, b18, b20, b23, b24, b26, b29, b30, b32, b41, b42, b45, b47]

theorem qTen_not_dvd_digits (w : List ℕ) (hw : w ⊆ [0, 1]) :
    ¬ qTen ∣ Nat.ofDigits (X : ℤ[X]) (1 :: w) := by
  apply qTen_not_dvd_newman
  · simp [Nat.ofDigits]
  · exact ofDigits_coeff_zero_one _ (by simpa using hw)

#print axioms qTen_not_dvd_newman
#print axioms qTen_not_dvd_digits
end Erdos406Quotient
