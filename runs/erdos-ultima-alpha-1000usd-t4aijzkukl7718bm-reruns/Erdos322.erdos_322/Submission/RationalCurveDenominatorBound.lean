import Submission.PositiveBinaryFormBound

/-! Denominator cancellation and counting bounds for fixed polynomial rational
families. The results below do not cover unrestricted quartic representations. -/
namespace Erdos322Research.RationalCurveDenominatorBound

open Polynomial Finset PositiveBinaryFormBound
set_option Elab.async false

/-- An affine Bezout certificate controls cancellation at primitive parameter
pairs when the denominator is monic. The numerator polynomials are homogenized
at their own degrees; factors of the second parameter are units modulo the
positive denominator value. -/
theorem denominator_dvd_fixed_multiple {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (hf : f.Monic)
    (hbez : (∑ i, A i*g i)+B*f = Polynomial.C (C : ℤ))
    {a b n L : ℕ} (hn : 0 < n) (hab : a.Coprime b)
    (hval : binaryValue f a b=(n : ℤ))
    (hnum : ∀ i, (n : ℤ) ∣ (L : ℤ)*binaryValue (g i) a b) : n ∣ C*L := by
  letI : NeZero n := ⟨hn.ne'⟩
  let r : ZMod n := (slope n (a,b) : ℕ)
  have hb := second_coprime_value f hf hab hval
  have hu : IsUnit (b : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr hb
  have hr : r*(b : ZMod n)=a := by
    have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (slope_mul hn hb (a := a))
    simpa only [Nat.cast_mul] using hh
  have hfzero : f.eval₂ (Int.castRingHom (ZMod n)) r=0 := by
    have hh := binaryValue_ratio f r hr
    rw [hval] at hh
    apply (hu.pow f.natDegree).mul_left_cancel
    simpa using hh.symm
  have hgzero (i : ι) : (L : ZMod n)*(g i).eval₂ (Int.castRingHom (ZMod n)) r=0 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr (hnum i)
    simp only [Int.cast_mul, Int.cast_natCast] at hh
    rw [binaryValue_ratio (g i) r hr] at hh
    apply (hu.pow (g i).natDegree).mul_left_cancel
    simpa only [mul_zero, mul_left_comm] using hh
  have hpoly := congrArg (Polynomial.eval₂ (Int.castRingHom (ZMod n)) r) hbez
  simp only [eval₂_add, eval₂_mul, eval₂_finset_sum, eval₂_C] at hpoly
  have hm := congrArg (fun x : ZMod n => (L : ZMod n)*x) hpoly
  simp only [hfzero, mul_zero, add_zero, Finset.mul_sum] at hm
  have hs : (∑ i, (L : ZMod n)*
      ((A i).eval₂ (Int.castRingHom (ZMod n)) r *
       (g i).eval₂ (Int.castRingHom (ZMod n)) r))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [mul_left_comm, hgzero, mul_zero]
  rw [hs] at hm
  apply (ZMod.natCast_eq_zero_iff _ n).mp
  simpa only [Nat.cast_mul, map_natCast, mul_comm] using hm.symm

/-- Uniform control of the full finite parameter set after cancellation.
The second Bezout certificate is for the derivative of the denominator, and
the fixed coercivity condition prevents large parameter pairs of small value. -/
theorem primitive_parameter_bound {ι : Type*} [Fintype ι]
    (f U V B : ℤ[X]) (g A : ι → ℤ[X]) (D C H : ℕ)
    (hf : f.Monic) (hd : 3 ≤ f.natDegree) (hD : 0 < D) (hC : 0 < C)
    (hder : U*f+V*f.derivative = Polynomial.C (D : ℤ))
    (hbez : (∑ i, A i*g i)+B*f = Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < binaryValue f a.1 a.2) →
      (∀ a ∈ S, ∀ i, ((binaryValue f a.1 a.2).toNat : ℤ) ∣
        (L : ℤ)*binaryValue (g i) a.1 a.2) →
      (∀ a ∈ S, (a.1+a.2)^f.natDegree ≤ H*(binaryValue f a.1 a.2).toNat) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := primitive_divisor_fibers_subpolynomial f U V hf hd D H hD hder ε hε
  refine ⟨K*(C : ℝ)^ε, by positivity, ?_⟩
  intro S L hL hprim hpos hnum hheight
  have hh := hbound S (C*L) (mul_pos hC hL) hprim hpos (by
    intro a ha
    have hn : 0 < (binaryValue f a.1 a.2).toNat := by
      have hh := hpos a ha
      omega
    exact denominator_dvd_fixed_multiple f B g A C hf hbez hn (hprim a ha)
      (Int.toNat_of_nonneg (hpos a ha).le).symm (hnum a ha)) hheight
  simpa only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg C) (Nat.cast_nonneg L),
    mul_assoc] using hh

lemma binaryValue_cast_ratio (f : ℤ[X]) (a b : ℕ) (hb : 0 < b) :
    (binaryValue f a b : ℚ) =
      (b : ℚ)^f.natDegree * f.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b) := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self f.natDegree)]
  unfold binaryValue
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ f.natDegree := by simpa using Finset.mem_range.mp hj
  have hp : (b : ℚ)^f.natDegree = (b : ℚ)^j*(b : ℚ)^(f.natDegree-j) := by
    rw [← pow_add, Nat.add_sub_of_le hjd]
  rw [hp, div_pow]
  change _ = ((b : ℚ)^j*(b : ℚ)^(f.natDegree-j))*
    ((f.coeff j : ℚ)*((a : ℚ)^j/(b : ℚ)^j))
  field_simp

/-- Actual integrality of a scaled rational coordinate implies the modular
numerator condition used above, despite the differing polynomial degrees. -/
theorem integer_scaled_value_implies_divisibility (f g : ℤ[X]) (hf : f.Monic)
    (hdeg : g.natDegree ≤ f.natDegree) {a b n L : ℕ}
    (hb : 0 < b) (hn : 0 < n) (hab : a.Coprime b)
    (hval : binaryValue f a b=(n : ℤ))
    (hint : ∃ z : ℤ, (L : ℚ)*g.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b) /
      f.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)=z) :
    (n : ℤ) ∣ (L : ℤ)*binaryValue g a b := by
  obtain ⟨z,hz⟩ := hint
  have hfq := binaryValue_cast_ratio f a b hb
  have hgq := binaryValue_cast_ratio g a b hb
  rw [hval] at hfq
  simp only [Int.cast_natCast] at hfq
  have hf0 : f.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hfq
    exact (by exact_mod_cast hn.ne' : (n : ℚ) ≠ 0) hfq
  have hz' := (div_eq_iff hf0).mp hz
  have he : (L : ℚ)*(b : ℚ)^(f.natDegree-g.natDegree)*(binaryValue g a b : ℚ) =
      (n : ℚ)*z := by
    calc
      _ = (L : ℚ)*(b : ℚ)^(f.natDegree-g.natDegree)*
        ((b : ℚ)^g.natDegree*g.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)) := by rw [hgq]
      _ = (b : ℚ)^f.natDegree*
        ((L : ℚ)*g.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)) := by
        rw [show (L : ℚ)*(b : ℚ)^(f.natDegree-g.natDegree)*
          ((b : ℚ)^g.natDegree*g.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)) =
          ((b : ℚ)^(f.natDegree-g.natDegree)*(b : ℚ)^g.natDegree)*
          ((L : ℚ)*g.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)) by ring,
          ← pow_add, Nat.sub_add_cancel hdeg]
      _ = (b : ℚ)^f.natDegree*(z*f.eval₂ (Int.castRingHom ℚ) ((a : ℚ)/b)) := by rw [hz']
      _ = (n : ℚ)*z := by rw [hfq]; ring
  have hez : (L : ℤ)*(b : ℤ)^(f.natDegree-g.natDegree)*binaryValue g a b=(n : ℤ)*z := by
    exact_mod_cast he
  have hdvd : (n : ℤ) ∣ (b : ℤ)^(f.natDegree-g.natDegree)*((L : ℤ)*binaryValue g a b) := by
    refine ⟨z,?_⟩
    linear_combination hez
  have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hdvd
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] at hzero
  have hu : IsUnit (b : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr
    (second_coprime_value f hf hab hval)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
  simp only [Int.cast_mul, Int.cast_natCast]
  apply (hu.pow (f.natDegree-g.natDegree)).mul_left_cancel
  simpa only [mul_zero] using hzero

/-- A fixed rational polynomial family satisfying the two explicit Bezout
certificates and a coercivity bound contributes only subpolynomially many
primitive nonnegative parameter pairs at a common integral scale. -/
theorem rational_parameter_bound {ι : Type*} [Fintype ι]
    (f U V B : ℤ[X]) (g A : ι → ℤ[X]) (D C H : ℕ)
    (hf : f.Monic) (hd : 3 ≤ f.natDegree) (hD : 0 < D) (hC : 0 < C)
    (hdeg : ∀ i, (g i).natDegree ≤ f.natDegree)
    (hder : U*f+V*f.derivative = Polynomial.C (D : ℤ))
    (hbez : (∑ i, A i*g i)+B*f = Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, a.1.Coprime a.2) →
      (∀ a ∈ S, 0 < a.2) →
      (∀ a ∈ S, 0 < binaryValue f a.1 a.2) →
      (∀ a ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) /
          f.eval₂ (Int.castRingHom ℚ) ((a.1 : ℚ)/a.2) = z) →
      (∀ a ∈ S, (a.1+a.2)^f.natDegree ≤ H*(binaryValue f a.1 a.2).toNat) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := primitive_parameter_bound f U V B g A D C H hf hd hD hC
    hder hbez ε hε
  refine ⟨K,hK,?_⟩
  intro S L hL hprim hbpos hpos hint hheight
  apply hbound S L hL hprim hpos _ hheight
  intro a ha i
  have hn : 0 < (binaryValue f a.1 a.2).toNat := by
    have hh := hpos a ha
    omega
  exact integer_scaled_value_implies_divisibility f (g i) hf (hdeg i)
    (hbpos a ha) hn (hprim a ha) (Int.toNat_of_nonneg (hpos a ha).le).symm (hint a ha i)

end Erdos322Research.RationalCurveDenominatorBound
