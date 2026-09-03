import Submission.CubicSmallPrimeCancellation

/-! The three cancellation divisors have disjoint prime support away from 6.
Consequently their product gives exactly the prime-to-6 part of the raw gcd.
This is an arithmetic description, not a density estimate. -/

namespace Erdos1206.CubicBaseLocus

def locusDivisor0 (a b t : ℤ) : ℕ := Int.gcd t (Q a b)
def locusDivisor1 (a b t : ℤ) : ℕ := Int.gcd b (t^2+3*a^2)
def locusDivisor2 (a b t : ℤ) : ℕ := Int.gcd (2*a-b) (t^2+3*a^2)
def locusProduct (a b t : ℤ) : ℕ :=
  locusDivisor0 a b t * locusDivisor1 a b t * locusDivisor2 a b t

lemma locus_divisors_pos {a b t : ℤ} (ht : 0 < t) :
    0 < locusDivisor0 a b t ∧ 0 < locusDivisor1 a b t ∧ 0 < locusDivisor2 a b t := by
  have hN : t^2+3*a^2 ≠ 0 := ne_of_gt (by nlinarith [sq_pos_of_pos ht,sq_nonneg a])
  exact ⟨Int.gcd_pos_of_ne_zero_left _ ht.ne',
    Int.gcd_pos_of_ne_zero_right _ hN,Int.gcd_pos_of_ne_zero_right _ hN⟩

/-- Two different base-locus divisors cannot share a prime other than 2 or 3. -/
lemma prime_locus_disjoint {a b t : ℤ}
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (¬ (p ∣ locusDivisor0 a b t ∧ p ∣ locusDivisor1 a b t)) ∧
    (¬ (p ∣ locusDivisor0 a b t ∧ p ∣ locusDivisor2 a b t)) ∧
    (¬ (p ∣ locusDivisor1 a b t ∧ p ∣ locusDivisor2 a b t)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have hnon : ¬ ((a : ZMod p)=0 ∧ (b : ZMod p)=0 ∧ (t : ZMod p)=0) := by
    rintro ⟨ha,hb,ht⟩
    exact triple_primitive_at_prime hprim hp
      ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
        (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb,
        (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp ht⟩
  have h0 (h : p ∣ locusDivisor0 a b t) :
      (t : ZMod p)=0 ∧ Q (a : ZMod p) b=0 := by
    obtain ⟨ht,hq⟩ := Int.dvd_gcd_iff.mp h
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd t p).mpr ht,
      by simpa [Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (Q a b) p).mpr hq⟩
  have h1 (h : p ∣ locusDivisor1 a b t) :
      (b : ZMod p)=0 ∧ (t : ZMod p)^2+3*(a : ZMod p)^2=0 := by
    obtain ⟨hb,hn⟩ := Int.dvd_gcd_iff.mp h
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr hb,
      by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (t^2+3*a^2) p).mpr hn⟩
  have h2' (h : p ∣ locusDivisor2 a b t) :
      (b : ZMod p)=2*(a : ZMod p) ∧ (t : ZMod p)^2+3*(a : ZMod p)^2=0 := by
    obtain ⟨hb,hn⟩ := Int.dvd_gcd_iff.mp h
    have hbb : 2*(a : ZMod p)-(b : ZMod p)=0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (2*a-b) p).mpr hb
    exact ⟨(sub_eq_zero.mp hbb).symm,
      by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (t^2+3*a^2) p).mpr hn⟩
  constructor
  · rintro ⟨hd0,hd1⟩
    obtain ⟨ht,hq⟩ := h0 hd0
    obtain ⟨hb,hn⟩ := h1 hd1
    have ha : (a : ZMod p)=0 := by
      have hh : (a : ZMod p)^2=0 := by simpa [Q,hb] using hq
      exact eq_zero_of_pow_eq_zero hh
    exact hnon ⟨ha,hb,ht⟩
  constructor
  · rintro ⟨hd0,hd2⟩
    obtain ⟨ht,hq⟩ := h0 hd0
    obtain ⟨hb,hn⟩ := h2' hd2
    have ha : (a : ZMod p)=0 := by
      have hh : 3*(a : ZMod p)^2=0 := by simpa [ht] using hn
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left h3)
    exact hnon ⟨ha,by simp [hb,ha],ht⟩
  · rintro ⟨hd1,hd2⟩
    obtain ⟨hb,hn⟩ := h1 hd1
    obtain ⟨hb',_⟩ := h2' hd2
    have ha : (a : ZMod p)=0 := by
      have hh : 2*(a : ZMod p)=0 := by rw [← hb',hb]
      exact (mul_eq_zero.mp hh).resolve_left h2
    have ht : (t : ZMod p)=0 := by
      have hh : (t : ZMod p)^2=0 := by simpa [ha] using hn
      exact eq_zero_of_pow_eq_zero hh
    exact hnon ⟨ha,hb,ht⟩

/-- Away from 2 and 3, cancellation is the product, not merely the maximum,
of the three base-locus gcds. -/
theorem certificate_factorization_locus_product {a b t g : ℤ} {x y z w : ℕ}
    (ht : 0 < t) (hg : 0 < g)
    (hprim : Nat.gcd (Int.gcd a b) t.natAbs = 1)
    (hpRoots : Nat.gcd (Nat.gcd x y) (Nat.gcd z w) = 1)
    (hA : A a b t = g*x) (hB : B a b t = g*y)
    (hC : C a b t = g*z) (hD : D a b t = g*w)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    g.natAbs.factorization p = (locusProduct a b t).factorization p := by
  obtain ⟨h0,h1,h2⟩ := locus_divisors_pos (a := a) (b := b) ht
  have hg0 : g.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hg.ne'
  have he (k : ℕ) : p^k ∣ g.natAbs ↔
      p^k ∣ locusDivisor0 a b t ∨ p^k ∣ locusDivisor1 a b t ∨ p^k ∣ locusDivisor2 a b t := by
    rw [← Int.natCast_dvd,Nat.cast_pow,
      certificate_prime_power_iff hprim hpRoots hA hB hC hD hp hp2 hp3 k]
    simp only [locusDivisor0,locusDivisor1,locusDivisor2,Int.dvd_gcd_iff,Nat.cast_pow]
  have hf (k : ℕ) : k ≤ g.natAbs.factorization p ↔
      k ≤ max ((locusDivisor0 a b t).factorization p)
        (max ((locusDivisor1 a b t).factorization p) ((locusDivisor2 a b t).factorization p)) := by
    simpa only [hp.pow_dvd_iff_le_factorization hg0,
      hp.pow_dvd_iff_le_factorization h0.ne',hp.pow_dvd_iff_le_factorization h1.ne',
      hp.pow_dvd_iff_le_factorization h2.ne',le_max_iff] using he k
  have hmax : g.natAbs.factorization p =
      max ((locusDivisor0 a b t).factorization p)
        (max ((locusDivisor1 a b t).factorization p) ((locusDivisor2 a b t).factorization p)) :=
    Nat.le_antisymm ((hf _).mp le_rfl) ((hf _).mpr le_rfl)
  rw [locusProduct,Nat.factorization_mul (Nat.mul_pos h0 h1).ne' h2.ne',
    Nat.factorization_mul h0.ne' h1.ne']
  simp only [Finsupp.add_apply]
  rw [hmax]
  obtain ⟨h01,h02,h12⟩ := prime_locus_disjoint hprim hp hp2 hp3
  by_cases hd0 : p ∣ locusDivisor0 a b t
  · have hz1 := Nat.factorization_eq_zero_of_not_dvd (fun hd1 => h01 ⟨hd0,hd1⟩)
    have hz2 := Nat.factorization_eq_zero_of_not_dvd (fun hd2 => h02 ⟨hd0,hd2⟩)
    simp [hz1,hz2]
  · have hz0 := Nat.factorization_eq_zero_of_not_dvd hd0
    by_cases hd1 : p ∣ locusDivisor1 a b t
    · have hz2 := Nat.factorization_eq_zero_of_not_dvd (fun hd2 => h12 ⟨hd1,hd2⟩)
      simp [hz0,hz2]
    · have hz1 := Nat.factorization_eq_zero_of_not_dvd hd1
      simp [hz0,hz1]

#print axioms prime_locus_disjoint
#print axioms certificate_factorization_locus_product

end Erdos1206.CubicBaseLocus
