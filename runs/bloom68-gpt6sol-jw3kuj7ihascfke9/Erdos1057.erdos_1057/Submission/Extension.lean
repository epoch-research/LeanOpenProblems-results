import Submission.Korselt

/-! A prime extension criterion for Carmichael numbers. -/

namespace Erdos1057

private theorem dvd_mul_sub_one_of_dvd_sub_one {d a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hda : d ∣ a - 1) (hdb : d ∣ b - 1) :
    d ∣ a * b - 1 := by
  have ha' : a ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' ha).mpr hda).symm
  have hb' : b ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' hb).mpr hdb).symm
  have hab' : a * b ≡ 1 [MOD d] := by simpa using ha'.mul hb'
  exact (Nat.modEq_iff_dvd' (Nat.mul_pos (by omega : 0 < a) (by omega : 0 < b))).mp hab'.symm

private theorem dvd_sub_one_of_dvd_mul_sub_one {d a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hda : d ∣ a - 1) (hdab : d ∣ a * b - 1) :
    d ∣ b - 1 := by
  have ha' : a ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' ha).mpr hda).symm
  have hab' : a * b ≡ 1 [MOD d] :=
    ((Nat.modEq_iff_dvd' (Nat.mul_pos (by omega : 0 < a) (by omega : 0 < b))).mpr hdab).symm
  have hb' : b ≡ 1 [MOD d] := by
    have h : a * b ≡ b [MOD d] := by simpa using ha'.mul (Nat.ModEq.refl b)
    exact h.symm.trans hab'
  exact (Nat.modEq_iff_dvd' hb).mp hb'.symm

/-- If `n` is Carmichael and `q` is a new prime, the precise condition for
`n * q` to be Carmichael is the two congruences in the statement. -/
theorem isCarmichael_mul_prime_iff {n q : ℕ}
    (hn : IsCarmichael n) (hq : Nat.Prime q) (hqnot : ¬q ∣ n) :
    IsCarmichael (n * q) ↔
      ArithmeticFunction.Carmichael n ∣ q - 1 ∧ q - 1 ∣ n - 1 := by
  have hnk := (isCarmichael_iff_korselt n).mp hn
  have hn1 : 1 ≤ n := hnk.1.1.le
  have hq1 : 1 ≤ q := hq.one_le
  constructor
  · intro hnq
    have hLamprod : ArithmeticFunction.Carmichael n ∣ n * q - 1 :=
      (ArithmeticFunction.carmichael_dvd (dvd_mul_right n q)).trans
        (isCarmichael_lambda_dvd_sub_one hnq)
    have hLamq : ArithmeticFunction.Carmichael n ∣ q - 1 :=
      dvd_sub_one_of_dvd_mul_sub_one hn1 hq1
        (isCarmichael_lambda_dvd_sub_one hn) hLamprod
    have hqn : q - 1 ∣ n - 1 :=
      isCarmichael_cofactor_constraint hnq hq (by ac_rfl : n * q = q * n)
    exact ⟨hLamq, hqn⟩
  · rintro ⟨hLamq, hqn⟩
    have hcop : n.Coprime q := (hq.coprime_iff_not_dvd.mpr hqnot).symm
    have hLamprod : ArithmeticFunction.Carmichael (n * q) ∣ n * q - 1 := by
      rw [ArithmeticFunction.carmichael_mul hcop, carmichael_at_prime hq]
      apply Nat.lcm_dvd
      · exact dvd_mul_sub_one_of_dvd_sub_one hn1 hq1
          (isCarmichael_lambda_dvd_sub_one hn) hLamq
      · exact dvd_mul_sub_one_of_dvd_sub_one hn1 hq1 hqn (dvd_refl _)
    apply (isCarmichael_iff_korselt (n * q)).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨by nlinarith [hnk.1.1, hq.two_le],
        Nat.not_prime_mul (by omega : n ≠ 1) hq.ne_one⟩
    · exact (Nat.squarefree_mul hcop).mpr ⟨hnk.2.1, hq.squarefree⟩
    · intro p hp hpnq
      rw [← carmichael_at_prime hp]
      exact (ArithmeticFunction.carmichael_dvd hpnq).trans hLamprod

end Erdos1057
