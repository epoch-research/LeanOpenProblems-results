import Submission.MonicEvenRationalFamilyBound

/-! Normalization of nonmonic positive binary forms, including the arithmetic
reduction of parameter pairs. These remain fixed-form divisor-fiber bounds. -/
namespace Erdos322Research.NormalizedBinaryFormBound

open Polynomial Finset PositiveBinaryFormBound PositiveBinaryFormCoercivity
open MonicBinaryDivisorBound RationalCurveDenominatorBound
set_option Elab.async false

/-- Multiply the numerator parameter by A, then reduce the pair. -/
def primitiveScale (A : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (A*p.1 / (A*p.1).gcd p.2, p.2 / (A*p.1).gcd p.2)

lemma primitiveScale_primitive (A : ℕ) (p : ℕ × ℕ) (hp : 0 < p.2) :
    (primitiveScale A p).1.Coprime (primitiveScale A p).2 :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hp)

lemma primitiveScale_second_pos (A : ℕ) (p : ℕ × ℕ) (hp : 0 < p.2) :
    0 < (primitiveScale A p).2 :=
  Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_right _ _))
    (Nat.gcd_pos_of_pos_right _ hp)

lemma primitiveScale_first_mul (A : ℕ) (p : ℕ × ℕ) :
    (A*p.1).gcd p.2*(primitiveScale A p).1=A*p.1 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

lemma primitiveScale_second_mul (A : ℕ) (p : ℕ × ℕ) :
    (A*p.1).gcd p.2*(primitiveScale A p).2=p.2 :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

lemma primitiveScale_cross (A : ℕ) (p : ℕ × ℕ) (hp : 0 < p.2) :
    A*p.1*(primitiveScale A p).2=(primitiveScale A p).1*p.2 := by
  have hg : 0 < (A*p.1).gcd p.2 := Nat.gcd_pos_of_pos_right _ hp
  apply Nat.mul_left_cancel hg
  calc
    (A*p.1).gcd p.2*(A*p.1*(primitiveScale A p).2) =
        (A*p.1)*((A*p.1).gcd p.2*(primitiveScale A p).2) := by ring
    _ = (A*p.1)*p.2 := by rw [primitiveScale_second_mul]
    _ = ((A*p.1).gcd p.2*(primitiveScale A p).1)*p.2 := by rw [primitiveScale_first_mul]
    _ = _ := by ring

lemma primitiveScale_injective_on (A : ℕ) (hA : 0 < A) :
    Set.InjOn (primitiveScale A) {p : ℕ × ℕ | p.1.Coprime p.2 ∧ 0 < p.2} := by
  intro p hp q hq he
  have h₁ := primitiveScale_cross A p hp.2
  have h₂ := primitiveScale_cross A q hq.2
  have hs : 0 < (primitiveScale A p).2 := primitiveScale_second_pos A p hp.2
  rw [← he] at h₂
  have hcross : p.1*q.2=q.1*p.2 := by
    apply Nat.mul_left_cancel (mul_pos hA hs)
    calc
      (A*(primitiveScale A p).2)*(p.1*q.2) =
          (A*p.1*(primitiveScale A p).2)*q.2 := by ring
      _ = ((primitiveScale A p).1*p.2)*q.2 := by rw [h₁]
      _ = ((primitiveScale A p).1*q.2)*p.2 := by ring
      _ = (A*q.1*(primitiveScale A p).2)*p.2 := by rw [h₂]
      _ = _ := by ring
  exact primitive_proportional hp.1 hq.1 hcross

lemma binaryValue_smul (f : ℤ[X]) (s a b : ℕ) :
    binaryValue f (s*a) (s*b)=(s : ℤ)^f.natDegree*binaryValue f a b := by
  have hh := realValue_smul f (s : ℝ) (a : ℝ) (b : ℝ)
  rw [← Nat.cast_mul, ← Nat.cast_mul, realValue_nat, realValue_nat] at hh
  exact_mod_cast hh

lemma normalized_binaryValue (f : ℤ[X]) (hd : 0 < f.natDegree)
    (A : ℕ) (hA : f.leadingCoeff=(A : ℤ)) (a b : ℕ) :
    binaryValue f.integralNormalization (A*a) b =
      (A : ℤ)^(f.natDegree-1)*binaryValue f a b := by
  unfold binaryValue
  rw [Polynomial.natDegree_integralNormalization, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hc := integralNormalization_coeff_mul_leadingCoeff_pow (p := f) j hd
  rw [hA] at hc
  push_cast
  rw [mul_pow]
  calc
    f.integralNormalization.coeff j*((A : ℤ)^j*(a : ℤ)^j)*(b : ℤ)^(f.natDegree-j) =
        (f.integralNormalization.coeff j*(A : ℤ)^j)*(a : ℤ)^j*(b : ℤ)^(f.natDegree-j) := by ring
    _ = _ := by rw [hc]; ring

lemma normalization_no_real_zero (f : ℤ[X]) (hd : 0 < f.natDegree)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0) :
    ∀ t : ℝ, f.integralNormalization.eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  have hc : (f.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hf
  intro t
  have he := integralNormalization_eval₂_leadingCoeff_mul (p := f) hd
    (Int.castRingHom ℝ) (t/(f.leadingCoeff : ℝ))
  simp only [Int.coe_castRingHom, mul_div_cancel₀ _ hc] at he
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hc) (hnoroot _)

lemma positive_leading_binaryValue (f : ℤ[X]) (hd : 0 < f.natDegree)
    (hpos : 0 < f.leadingCoeff)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (a b : ℕ) (hb : 0 < b) : 0 < binaryValue f a b := by
  let A : ℕ := f.leadingCoeff.toNat
  have hA : f.leadingCoeff=(A : ℤ) := (Int.toNat_of_nonneg hpos.le).symm
  have hAp : 0 < A := by dsimp [A]; omega
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  have hh := binaryValue_positive f.integralNormalization (monic_integralNormalization hf)
    (normalization_no_real_zero f hd hnoroot) (A*a) b (by omega)
  rw [normalized_binaryValue f hd A hA] at hh
  exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hAp) _)).mp hh

/-- A fixed positive-leading nonmonic form has the same divisor-fiber bound
as a monic form, after an injective reduction of the parameter pairs. -/
theorem positive_leading_divisor_fibers_subpolynomial (f : ℤ[X])
    (hd : 0 < f.natDegree) (hlc : 0 < f.leadingCoeff)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, (binaryValue f a.1 a.2).toNat ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  classical
  let A : ℕ := f.leadingCoeff.toNat
  let M : ℕ := A^(f.natDegree-1)
  have hA : f.leadingCoeff=(A : ℤ) := (Int.toNat_of_nonneg hlc.le).symm
  have hAp : 0 < A := by dsimp [A]; omega
  have hMp : 0 < M := pow_pos hAp _
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  let h := f.integralNormalization
  have hh : h.Monic := monic_integralNormalization hf
  have hdh : 0 < h.natDegree := by simpa only [h,natDegree_integralNormalization] using hd
  have hhnoroot := normalization_no_real_zero f hd hnoroot
  obtain ⟨K,hK,hbound⟩ := monic_divisor_fibers_subpolynomial h hh hdh hhnoroot ε hε
  refine ⟨K*(M : ℝ)^ε, by positivity, ?_⟩
  intro S L hL hprim hbpos hdvd
  let T := S.image (primitiveScale A)
  have hcard : T.card=S.card := Finset.card_image_of_injOn (by
    intro a ha b hb hab
    exact primitiveScale_injective_on A hAp ⟨hprim a ha,hbpos a ha⟩
      ⟨hprim b hb,hbpos b hb⟩ hab)
  have hTprim (p : ℕ × ℕ) (hp : p ∈ T) : p.1.Coprime p.2 := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact primitiveScale_primitive A a (hbpos a ha)
  have hTpos (p : ℕ × ℕ) (hp : p ∈ T) : 0 < p.2 := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact primitiveScale_second_pos A a (hbpos a ha)
  have hTdvd (p : ℕ × ℕ) (hp : p ∈ T) : (binaryValue h p.1 p.2).toNat ∣ M*L := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    let p := primitiveScale A a
    let c := (A*a.1).gcd a.2
    have hc1 : c*p.1=A*a.1 := primitiveScale_first_mul A a
    have hc2 : c*p.2=a.2 := primitiveScale_second_mul A a
    have he := binaryValue_smul h c p.1 p.2
    rw [hc1,hc2] at he
    have he' : (M : ℤ)*binaryValue f a.1 a.2=(c : ℤ)^h.natDegree*binaryValue h p.1 p.2 := by
      rw [← he]
      exact (normalized_binaryValue f hd A hA a.1 a.2).symm
    have hdZ : binaryValue h p.1 p.2 ∣ (M : ℤ)*binaryValue f a.1 a.2 :=
      ⟨(c : ℤ)^h.natDegree, by rw [he']; ring⟩
    have hpH : 0 < binaryValue h p.1 p.2 := binaryValue_positive h hh hhnoroot p.1 p.2
      (by have := primitiveScale_second_pos A a (hbpos a ha); change 0 < p.2 at this; omega)
    have hpF : 0 < binaryValue f a.1 a.2 := positive_leading_binaryValue f hd hlc hnoroot
      a.1 a.2 (hbpos a ha)
    have hdN : (binaryValue h p.1 p.2).toNat ∣ M*(binaryValue f a.1 a.2).toNat := by
      apply Int.natCast_dvd_natCast.mp
      simpa only [Nat.cast_mul,Int.toNat_of_nonneg hpH.le,Int.toNat_of_nonneg hpF.le] using hdZ
    exact hdN.trans (Nat.mul_dvd_mul_left M (hdvd a ha))
  have hb := hbound T (M*L) (mul_pos hMp hL) hTprim hTpos hTdvd
  rw [hcard] at hb
  simpa only [Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg M) (Nat.cast_nonneg L), mul_assoc] using hb

lemma binaryValue_neg (f : ℤ[X]) (a b : ℕ) :
    binaryValue (-f) a b= -binaryValue f a b := by
  simp only [binaryValue,natDegree_neg,coeff_neg,neg_mul,Finset.sum_neg_distrib]

lemma natAbs_eq_toNat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : z.natAbs=z.toNat := by
  have he := (Int.natAbs_of_nonneg hz).trans (Int.toNat_of_nonneg hz).symm
  exact_mod_cast he

/-- The nonmonic bound has no leading-coefficient sign restriction when the
absolute denominator value is used. -/
theorem divisor_fibers_subpolynomial (f : ℤ[X]) (hd : 0 < f.natDegree)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, (binaryValue f a.1 a.2).natAbs ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  by_cases hlc : 0 < f.leadingCoeff
  · obtain ⟨K,hK,hbound⟩ := positive_leading_divisor_fibers_subpolynomial f hd hlc hnoroot ε hε
    refine ⟨K,hK,?_⟩
    intro S L hL hprim hbpos hdvd
    apply hbound S L hL hprim hbpos
    intro a ha
    have hp := positive_leading_binaryValue f hd hlc hnoroot a.1 a.2 (hbpos a ha)
    simpa only [natAbs_eq_toNat_of_nonneg hp.le] using hdvd a ha
  · have hf : f ≠ 0 := by intro hz; simp [hz] at hd
    have hcz := leadingCoeff_ne_zero.mpr hf
    have hneg : 0 < (-f).leadingCoeff := by rw [leadingCoeff_neg]; omega
    have hdeg : 0 < (-f).natDegree := by simpa using hd
    have hroots (t : ℝ) : (-f).eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
      simpa only [eval₂_neg,neg_ne_zero] using hnoroot t
    obtain ⟨K,hK,hbound⟩ := positive_leading_divisor_fibers_subpolynomial
      (-f) hdeg hneg hroots ε hε
    refine ⟨K,hK,?_⟩
    intro S L hL hprim hbpos hdvd
    apply hbound S L hL hprim hbpos
    intro a ha
    have hp := positive_leading_binaryValue (-f) hdeg hneg hroots a.1 a.2 (hbpos a ha)
    rw [← natAbs_eq_toNat_of_nonneg hp.le,binaryValue_neg,Int.natAbs_neg]
    exact hdvd a ha

end Erdos322Research.NormalizedBinaryFormBound
