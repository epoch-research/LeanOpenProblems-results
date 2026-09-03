import FormalConjecturesUtil

/-! Reflection using a smooth divisor and a prime, rather than two prime
labels. The construction produces an ascent and a descent in one finite
interval, but does not control coverage or multiplicity. It is not a proof
or disproof of Erdős 371. -/

namespace Erdos371DivisorPrimeReflection

abbrev P := Nat.maxPrimeFac

def sign (n : ℕ) : ℤ := if P n < P (n+1) then 1 else -1

lemma smooth_mul_lt {b k p : ℕ} (hb : 0 < b) (hk : 0 < k)
    (hbp : P b < p) (hkp : k < p) : P (b*k) < p := by
  rw [P, Nat.maxPrimeFac_mul hb.ne' hk.ne']
  exact max_lt hbp (Nat.maxPrimeFac_le.trans_lt hkp)

/-- The winning prime is not asserted to be preserved. -/
theorem reflection_of_coordinates {p b k a : ℕ} (hp : p.Prime)
    (hb : 1 < b) (hk : 0 < k) (hkp : k < p) (hbp : P b < p)
    (he : b*k+1 = p*a) :
    let r := b*k
    let t := p*(b-a)
    0 < r ∧ 0 < t ∧ r+t+1 = p*b ∧
      P r < P (r+1) ∧ P (t+1) < P t := by
  have ha : 0 < a := by nlinarith
  have hab : a < b := by
    have hk' : k+1 ≤ p := hkp
    have hh := Nat.mul_le_mul_left b hk'
    nlinarith
  have hba : 0 < b-a := Nat.sub_pos_of_lt hab
  have hpk : 0 < p-k := Nat.sub_pos_of_lt hkp
  have hk0 : p-k < p := Nat.sub_lt hp.pos hk
  have hdiff : p*(b-a) + p*a = p*b := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hab.le]
  have hdiff' : b*(p-k)+b*k = p*b := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hkp.le, mul_comm]
  have ht : p*(b-a)+1 = b*(p-k) := by omega
  have hlow := smooth_mul_lt (by omega : 0 < b) hk hbp hkp
  have hpR : p ≤ P (b*k+1) := Nat.le_maxPrimeFac (by omega) hp
    (he ▸ dvd_mul_right p a)
  have hpT : p ≤ P (p*(b-a)) := Nat.le_maxPrimeFac
    (Nat.mul_pos hp.pos hba).ne' hp (dvd_mul_right p (b-a))
  refine ⟨Nat.mul_pos (by omega) hk, Nat.mul_pos hp.pos hba,
    by omega, hlow.trans_le hpR, ?_⟩
  rw [ht]
  exact (smooth_mul_lt (by omega) hpk hbp hk0).trans_le hpT

lemma prime_coprime_smooth {p b : ℕ} (hp : p.Prime) (hb : 0 < b)
    (hbp : P b < p) : b.Coprime p := by
  apply Nat.Coprime.symm
  apply (hp.coprime_iff_not_dvd).mpr
  intro hd
  exact (not_le_of_gt hbp) (Nat.le_maxPrimeFac hb.ne' hp hd)

/-- Every prime with a nontrivial coprime smooth cofactor gives one opposite-
sign pair below their product. This is a statement about parameters, not an
injective pairing of all consecutive integers in that interval. -/
theorem exists_opposite_pair {p b : ℕ} (hp : p.Prime) (hb : 1 < b)
    (hbp : P b < p) :
    ∃ r t : ℕ, 0 < r ∧ 0 < t ∧ r+t+1 = p*b ∧
      b ∣ r ∧ p ∣ r+1 ∧ p ∣ t ∧ b ∣ t+1 ∧
      P r < P (r+1) ∧ P (t+1) < P t := by
  have hcop := prime_coprime_smooth hp (by omega : 0 < b) hbp
  let r := Nat.chineseRemainder hcop 0 (p-1)
  have hr : (r : ℕ) < b*p := Nat.chineseRemainder_lt_mul hcop _ _
    (by omega) hp.ne_zero
  have hbr : b ∣ (r : ℕ) := Nat.modEq_zero_iff_dvd.mp r.property.1
  have hpr : p ∣ (r : ℕ)+1 := by
    have hh := r.property.2.add_right 1
    rw [Nat.sub_add_cancel hp.one_lt.le] at hh
    exact Nat.modEq_zero_iff_dvd.mp
      (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)))
  obtain ⟨k, hk⟩ := hbr
  obtain ⟨a, ha⟩ := hpr
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hr0 : (r : ℕ) = 0 := by simpa [hk0] using hk
    have hh : p ∣ 1 := ⟨a, by simpa [hr0] using ha⟩
    exact hp.not_dvd_one hh
  have hkp : k < p := by
    rw [hk] at hr
    exact (Nat.mul_lt_mul_left (by omega : 0 < b)).mp hr
  have he : b*k+1 = p*a := by omega
  have hh := reflection_of_coordinates hp hb hkpos hkp hbp he
  dsimp only at hh
  refine ⟨b*k, p*(b-a), hh.1, hh.2.1, hh.2.2.1,
    dvd_mul_right b k, he ▸ dvd_mul_right p a,
    dvd_mul_right p (b-a), ?_, hh.2.2.2⟩
  have hdiv : b ∣ p*(b-a)+1 := by
    have hsum := hh.2.2.1
    have hbprod : b ∣ p*b := dvd_mul_left b p
    have hbsub := Nat.dvd_sub hbprod (dvd_mul_right b k)
    have heq : p*b-b*k = p*(b-a)+1 := by omega
    rwa [heq] at hbsub
  exact hdiv

/-- The new reflection can change the winning prime, and need not meet the
old product-of-two-largest-primes range condition. -/
lemma winner_can_increase :
    P 8 < P 9 ∧ P 16 < P 15 ∧ 8+15+1 = 3*8 ∧
      max (P 8) (P 9) = 3 ∧ max (P 15) (P 16) = 5 ∧
      ¬ 8+1 < P 8 * P 9 := by
  decide +kernel

/-- Merely retaining coprimality is insufficient. The parameters `p=2`,
`b=9` produce the two ascents at 9 and 8. -/
theorem smoothness_cannot_be_dropped :
    ¬ ∀ p b r t : ℕ, p.Prime → 1 < b → b.Coprime p →
      0 < r → 0 < t → r+t+1 = p*b → b ∣ r → p ∣ r+1 →
      sign r = -sign t := by
  intro h
  have hh := h 2 9 9 8 (by decide) (by omega) (by decide)
    (by omega) (by omega) (by omega) (by decide) (by decide)
  have hs : sign 9 = 1 ∧ sign 8 = 1 := by decide +kernel
  rw [hs.1, hs.2] at hh
  norm_num at hh

end Erdos371DivisorPrimeReflection

#print axioms Erdos371DivisorPrimeReflection.exists_opposite_pair
#print axioms Erdos371DivisorPrimeReflection.winner_can_increase
#print axioms Erdos371DivisorPrimeReflection.smoothness_cannot_be_dropped
