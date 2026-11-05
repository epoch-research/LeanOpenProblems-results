import Submission.Extension

/-!
# Gluing coprime Carmichael blocks

Korselt's criterion and the multiplicativity of the Carmichael function give an exact
criterion for adjoining a coprime squarefree block to a Carmichael number.  When both
blocks are Carmichael, the second congruence simplifies to a congruence modulo the
Carmichael function of the second block.
-/

namespace Erdos1057

-- The analogous helpers in `Submission.Extension` are private to that module.
private theorem dvd_mul_sub_one_of_dvd_sub_one {d a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hda : d ∣ a - 1) (hdb : d ∣ b - 1) :
    d ∣ a * b - 1 := by
  have ha' : a ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' ha).mpr hda).symm
  have hb' : b ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' hb).mpr hdb).symm
  have hab' : a * b ≡ 1 [MOD d] := by simpa using ha'.mul hb'
  exact (Nat.modEq_iff_dvd' (Nat.mul_pos (by omega : 0 < a) (by omega : 0 < b))).mp
    hab'.symm

private theorem dvd_sub_one_of_dvd_mul_sub_one {d a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hda : d ∣ a - 1) (hdab : d ∣ a * b - 1) :
    d ∣ b - 1 := by
  have ha' : a ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' ha).mpr hda).symm
  have hab' : a * b ≡ 1 [MOD d] :=
    ((Nat.modEq_iff_dvd' (Nat.mul_pos (by omega : 0 < a) (by omega : 0 < b))).mpr
      hdab).symm
  have hb' : b ≡ 1 [MOD d] := by
    have h : a * b ≡ b [MOD d] := by simpa using ha'.mul (Nat.ModEq.refl b)
    exact h.symm.trans hab'
  exact (Nat.modEq_iff_dvd' hb).mp hb'.symm

/-- Exact criterion for adjoining a coprime squarefree block `m` to a Carmichael
number `n`.  No lower bound on `m` beyond squarefreeness is required; in particular,
this applies when `m = 1`. -/
theorem isCarmichael_mul_squarefree_iff {n m : ℕ}
    (hn : IsCarmichael n) (hm : Squarefree m) (hcop : n.Coprime m) :
    IsCarmichael (n * m) ↔
      ArithmeticFunction.Carmichael n ∣ m - 1 ∧
        ArithmeticFunction.Carmichael m ∣ n * m - 1 := by
  have hnk := (isCarmichael_iff_korselt n).mp hn
  have hn1 : 1 ≤ n := hnk.1.1.le
  have hm1 : 1 ≤ m := by have := hm.ne_zero; omega
  constructor
  · intro hnm
    have hprod : ArithmeticFunction.Carmichael (n * m) ∣ n * m - 1 :=
      isCarmichael_lambda_dvd_sub_one hnm
    rw [ArithmeticFunction.carmichael_mul hcop] at hprod
    have hnprod : ArithmeticFunction.Carmichael n ∣ n * m - 1 :=
      (Nat.dvd_lcm_left _ _).trans hprod
    have hmprod : ArithmeticFunction.Carmichael m ∣ n * m - 1 :=
      (Nat.dvd_lcm_right _ _).trans hprod
    exact ⟨dvd_sub_one_of_dvd_mul_sub_one hn1 hm1
      (isCarmichael_lambda_dvd_sub_one hn) hnprod, hmprod⟩
  · rintro ⟨hnm, hmprod⟩
    have hnprod : ArithmeticFunction.Carmichael n ∣ n * m - 1 :=
      dvd_mul_sub_one_of_dvd_sub_one hn1 hm1 (isCarmichael_lambda_dvd_sub_one hn) hnm
    have hprod : ArithmeticFunction.Carmichael (n * m) ∣ n * m - 1 := by
      rw [ArithmeticFunction.carmichael_mul hcop]
      exact Nat.lcm_dvd hnprod hmprod
    apply (isCarmichael_iff_korselt (n * m)).mpr
    refine ⟨?_, (Nat.squarefree_mul hcop).mpr ⟨hnk.2.1, hm⟩, ?_⟩
    · refine ⟨by nlinarith [hnk.1.1, hm1], ?_⟩
      intro hp
      rcases Nat.prime_mul_iff.mp hp with ⟨hp, _⟩ | ⟨_, hn_one⟩
      · exact hnk.1.2 hp
      · exact (by omega : n ≠ 1) hn_one
    · intro p hp hpnm
      rw [← carmichael_at_prime hp]
      exact (ArithmeticFunction.carmichael_dvd hpnm).trans hprod

/-- For two coprime Carmichael blocks, the mutual divisibility conditions on
the Carmichael functions are necessary and sufficient for their product to be
Carmichael. -/
theorem isCarmichael_mul_coprime_iff {n m : ℕ}
    (hn : IsCarmichael n) (hm : IsCarmichael m) (hcop : n.Coprime m) :
    IsCarmichael (n * m) ↔
      ArithmeticFunction.Carmichael n ∣ m - 1 ∧
        ArithmeticFunction.Carmichael m ∣ n - 1 := by
  have hn1 : 1 ≤ n := ((isCarmichael_iff_korselt n).mp hn).1.1.le
  have hm1 : 1 ≤ m := ((isCarmichael_iff_korselt m).mp hm).1.1.le
  rw [isCarmichael_mul_squarefree_iff hn (isCarmichael_squarefree hm) hcop]
  constructor
  · rintro ⟨hnm, hmprod⟩
    refine ⟨hnm, ?_⟩
    apply dvd_sub_one_of_dvd_mul_sub_one hm1 hn1 (isCarmichael_lambda_dvd_sub_one hm)
    simpa only [Nat.mul_comm] using hmprod
  · rintro ⟨hnm, hmn⟩
    refine ⟨hnm, ?_⟩
    have h := dvd_mul_sub_one_of_dvd_sub_one hm1 hn1
      (isCarmichael_lambda_dvd_sub_one hm) hmn
    simpa only [Nat.mul_comm] using h

/-- Korselt's criterion for gluing two arbitrary coprime squarefree composite
blocks. Neither block has to be Carmichael. -/
theorem isCarmichael_mul_squarefree_blocks_iff {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hcop : a.Coprime b)
    (ha1 : 1 < a) (hb1 : 1 < b) :
    IsCarmichael (a * b) ↔
      Nat.lcm (ArithmeticFunction.Carmichael a) (ArithmeticFunction.Carmichael b) ∣
        a * b - 1 := by
  have hcomp : (a * b).Composite := by
    refine ⟨by nlinarith, ?_⟩
    intro hp
    rcases (Nat.prime_mul_iff.mp hp) with ⟨_, hb_eq⟩ | ⟨ha_eq, _⟩
    · omega
    · omega
  have hsq : Squarefree (a * b) := (Nat.squarefree_mul hcop).mpr ⟨ha, hb⟩
  constructor
  · intro h
    have hlambda := isCarmichael_lambda_dvd_sub_one h
    simpa only [ArithmeticFunction.carmichael_mul hcop] using hlambda
  · intro h
    apply (isCarmichael_iff_korselt (a * b)).mpr
    refine ⟨hcomp, hsq, ?_⟩
    intro p hp hpdvd
    rw [← carmichael_at_prime hp]
    have hlambda : ArithmeticFunction.Carmichael (a * b) ∣ a * b - 1 := by
      rw [ArithmeticFunction.carmichael_mul hcop]
      exact h
    exact (ArithmeticFunction.carmichael_dvd hpdvd).trans hlambda

end Erdos1057

#print axioms Erdos1057.isCarmichael_mul_squarefree_iff
#print axioms Erdos1057.isCarmichael_mul_coprime_iff
#print axioms Erdos1057.isCarmichael_mul_squarefree_blocks_iff
