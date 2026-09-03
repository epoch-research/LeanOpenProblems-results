import Submission.NormalizedBinaryFormBound

/-! Cancellation of denominators for nonmonic integer polynomial families.
The extra factors depend only on the leading coefficient and the fixed
Bezout certificate, not on the rational parameter or integral scale. -/
namespace Erdos322Research.NonmonicDenominatorCancellation

open Polynomial Finset PositiveBinaryFormBound RationalCurveDenominatorBound
open NormalizedBinaryFormBound
set_option Elab.async false

lemma binaryValue_mod_second_general (f : ℤ[X]) (a b : ℕ) :
    ((binaryValue f a b : ℤ) : ZMod b)=
      (f.leadingCoeff : ZMod b)*(a : ZMod b)^f.natDegree := by
  classical
  unfold binaryValue
  push_cast
  rw [Finset.sum_eq_single f.natDegree]
  · simp [Polynomial.coeff_natDegree]
  · intro j hj hne
    have hjd : j < f.natDegree := by
      have := Finset.mem_range.mp hj
      omega
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hjd)]
  · simp

/-- At a primitive parameter pair, only primes in the fixed leading
coefficient can obstruct cancellation of the second coordinate. -/
theorem gcd_second_value_dvd_leading (f : ℤ[X]) (a b : ℕ) (hab : a.Coprime b) :
    (binaryValue f a b).natAbs.gcd b ∣ f.leadingCoeff.natAbs := by
  let d := (binaryValue f a b).natAbs.gcd b
  have hdF : (d : ℤ) ∣ binaryValue f a b := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hdb : d ∣ b := Nat.gcd_dvd_right _ _
  have hbdiv : (b : ℤ) ∣ binaryValue f a b-f.leadingCoeff*(a : ℤ)^f.natDegree := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ b).mp
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [binaryValue_mod_second_general,sub_self]
  have hdsub := (show (d : ℤ) ∣ (b : ℤ) by exact_mod_cast hdb).trans hbdiv
  have hdprod : (d : ℤ) ∣ f.leadingCoeff*(a : ℤ)^f.natDegree := by
    convert dvd_sub hdF hdsub using 1
    ring
  have hnat : d ∣ f.leadingCoeff.natAbs*a^f.natDegree := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using
      Int.natCast_dvd.mp hdprod
  exact (((hab.of_dvd_right hdb).symm).pow_right _).dvd_of_dvd_mul_right hnat

lemma cancel_second_power {n b A K : ℕ} (m : ℕ)
    (hA : n.gcd b ∣ A) (h : n ∣ K*b^m) : n ∣ K*A^m := by
  have hg : n.gcd (b^m) ∣ (n.gcd b)^m := gcd_pow_right_dvd_pow_gcd
  have hn : n ∣ K*n.gcd (b^m) := dvd_mul_gcd_of_dvd_mul h
  exact hn.trans (Nat.mul_dvd_mul_left K (hg.trans (pow_dvd_pow_of_dvd hA m)))

/-- A fixed exponent sufficient to clear every coefficient in the numerator
Bezout certificate. -/
def certificateDegree {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (A : ι → ℤ[X]) : ℕ :=
  f.natDegree+max B.natDegree (Finset.univ.sup (fun i => (A i).natDegree))

/-- The raw homogenized denominator of a reduced nonmonic rational family
divides a fixed multiple of the common integral scale. -/
theorem denominator_dvd_fixed_multiple {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (hC : 0 < C)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    {a b L : ℕ} (hb : 0 < b) (hL : 0 < L) (hab : a.Coprime b)
    (hne : binaryValue f a b ≠ 0)
    (hint : ∀ i, ∃ z : ℤ,
      (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b) /
        f.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)=z) :
    (binaryValue f a b).natAbs ∣
      (C*f.leadingCoeff.natAbs^(certificateDegree f B A))*L := by
  classical
  let t : ℚ := (a : ℚ)/b
  let ev : ℤ[X] →+* ℚ := Polynomial.eval₂RingHom (Int.castRingHom ℚ) t
  have evC (c : ℤ) : ev (Polynomial.C c)=(c : ℚ) := Polynomial.eval₂_C _ _
  have hfe : ev f ≠ 0 := by
    intro hz
    have he := binaryValue_cast_ratio f a b hb
    change _ = _*ev f at he
    rw [hz,mul_zero] at he
    exact hne (by exact_mod_cast he)
  choose z hz using hint
  have hi (i : ι) : (L : ℚ)*ev (g i)=(z i : ℚ)*ev f :=
    (div_eq_iff hfe).mp (hz i)
  let Q : ℤ[X] := B*Polynomial.C (L : ℤ)+∑ i, A i*Polynomial.C (z i)
  have hev : ev f*ev Q=(C : ℚ)*L := by
    have he := congrArg ev hbez
    simp only [map_add,map_sum,map_mul,evC,Int.cast_natCast] at he
    change (∑ i, ev (A i)*ev (g i))+ev B*ev f=(C : ℚ) at he
    have hq : ev Q=ev B*(L : ℚ)+∑ i, ev (A i)*(z i : ℚ) := by
      simp only [Q,map_add,map_mul,map_sum,evC,Int.cast_natCast]
    rw [hq,mul_add,Finset.mul_sum]
    have hs : (∑ i, ev f*(ev (A i)*(z i : ℚ)))=
        (L : ℚ)*(∑ i, ev (A i)*ev (g i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        ev f*(ev (A i)*(z i : ℚ))=ev (A i)*((z i : ℚ)*ev f) := by ring
        _ = _ := by rw [← hi i]; ring
    rw [hs]
    calc
      _ = (L : ℚ)*((∑ i, ev (A i)*ev (g i))+ev B*ev f) := by ring
      _ = _ := by rw [he]; ring
  have hf : f ≠ 0 := by intro hf; apply hfe; simp [hf]
  have hQ : Q ≠ 0 := by
    intro hQ
    rw [hQ,map_zero,mul_zero] at hev
    have hp : (0 : ℚ) < (C : ℚ)*L := by exact_mod_cast mul_pos hC hL
    linarith
  let d : ℕ := max B.natDegree (Finset.univ.sup fun i => (A i).natDegree)
  have hQdeg : Q.natDegree ≤ d := by
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_C_le _ _).trans (le_max_left _ _)
    · apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_mul_C_le _ _).trans
        ((Finset.le_sup (f := fun i => (A i).natDegree) (Finset.mem_univ i)).trans
          (le_max_right _ _))
  have htotal : (f*Q).natDegree ≤ certificateDegree f B A :=
    natDegree_mul_le.trans (Nat.add_le_add_left hQdeg _)
  have hev' := binaryValue_cast_ratio (f*Q) a b hb
  rw [Polynomial.eval₂_mul] at hev'
  change _ = _*(ev f*ev Q) at hev'
  rw [hev,MonicDenominatorFactor.binaryValue_mul f Q hf hQ a b hb,Int.cast_mul] at hev'
  have heZ : binaryValue f a b*binaryValue Q a b=
      (C : ℤ)*(L : ℤ)*(b : ℤ)^(f*Q).natDegree := by
    exact_mod_cast (show (binaryValue f a b : ℚ)*(binaryValue Q a b : ℚ)=
      (C : ℚ)*(L : ℚ)*(b : ℚ)^(f*Q).natDegree by nlinarith [hev'])
  have hdZ : binaryValue f a b ∣ (C : ℤ)*(L : ℤ)*(b : ℤ)^(f*Q).natDegree :=
    ⟨binaryValue Q a b,heZ.symm⟩
  have hn : (binaryValue f a b).natAbs ∣ C*L*b^(f*Q).natDegree := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.mpr hdZ
  have hn' : (binaryValue f a b).natAbs ∣ C*L*b^(certificateDegree f B A) :=
    hn.trans (Nat.mul_dvd_mul_left (C*L) (pow_dvd_pow b htotal))
  have hc := cancel_second_power (certificateDegree f B A)
    (gcd_second_value_dvd_leading f a b hab) hn'
  simpa only [mul_right_comm C L] using hc

end Erdos322Research.NonmonicDenominatorCancellation
