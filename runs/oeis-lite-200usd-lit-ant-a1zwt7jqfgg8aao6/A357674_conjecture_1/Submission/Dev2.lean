import Submission.Build
import Submission.Carlitz

open Nat Finset BigOperators

namespace ZK

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

/-- For a `p`-integral rational, the denominator casts to a unit in `ZMod (p^k)`. -/
lemma den_isUnit (hk : 0 < k) {q : ℚ} (h : padicNorm p q ≤ 1) :
    IsUnit ((q.den : ZMod (p^k))) := by
  have hpp : p.Prime := Fact.out
  -- p does not divide q.den
  have hpd : ¬ (p ∣ q.den) := by
    intro hd
    -- then padicNorm of den < 1 forces padicNorm q > 1 unless p | num too, contradiction with reduced
    have hpn : ¬ (p:ℤ) ∣ q.num := by
      intro hpn
      have h1 : p ∣ q.num.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hpn
        rwa [Int.natAbs_natCast] at this
      have hg : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hd
      rw [q.reduced] at hg
      have := Nat.le_of_dvd one_pos hg
      have := hpp.two_le
      omega
    have hnum : padicNorm p ((q.num : ℤ) : ℚ) = 1 := (padicNorm.int_eq_one_iff q.num).2 hpn
    have hden_lt : padicNorm p ((q.den : ℕ) : ℚ) < 1 := (padicNorm.nat_lt_one_iff q.den).2 hd
    have hden_pos : 0 < padicNorm p ((q.den : ℕ) : ℚ) := by
      rcases (padicNorm.nonneg ((q.den : ℕ) : ℚ)).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have := padicNorm.zero_of_padicNorm_eq_zero heq.symm
        simp only [Nat.cast_eq_zero] at this
        exact q.den_nz this
    have hqeq : q = ((q.num : ℤ) : ℚ) / ((q.den : ℕ) : ℚ) := (Rat.num_div_den q).symm
    rw [hqeq, padicNorm.div, hnum] at h
    rw [div_le_one hden_pos] at h
    linarith
  -- p ∤ den → den is a unit mod p^k
  rw [ZMod.isUnit_iff_coprime]
  have hcop : Nat.Coprime q.den p := (hpp.coprime_iff_not_dvd.mpr hpd).symm
  exact hcop.pow_right k
