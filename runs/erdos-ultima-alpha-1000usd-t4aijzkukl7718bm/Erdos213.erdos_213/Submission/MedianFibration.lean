import FormalConjecturesUtil

/-! Exact obstruction for an automatic-square median-fibration construction.
This does not settle Erdős 213 or classify all rational points on the fibers. -/

namespace Erdos213.MedianFibration

noncomputable section

open QuadraticAlgebra Polynomial

lemma quadratic_square_iff {K : Type*} [Field K] [CharZero K]
    (a d : K) (ha : a ≠ 0) :
    IsSquare (algebraMap K (QuadraticAlgebra K a 0) d) ↔
      IsSquare d ∨ IsSquare (a*d) := by
  constructor
  · rintro ⟨z,hz⟩
    have hr := congrArg QuadraticAlgebra.re hz
    have hi := congrArg QuadraticAlgebra.im hz
    simp only [algebraMap_re, re_mul] at hr
    simp only [algebraMap_im, im_mul, zero_mul, add_zero] at hi
    have hprod : z.re*z.im = 0 := by
      have he : (2 : K)*(z.re*z.im) = 0 := by linear_combination -hi
      exact (mul_eq_zero.mp he).resolve_left (by norm_num)
    rcases mul_eq_zero.mp hprod with hre | him
    · right
      refine ⟨a*z.im, ?_⟩
      rw [hre] at hr
      linear_combination a*hr
    · left
      exact ⟨z.re, by simpa [him] using hr⟩
  · rintro (⟨z,hz⟩ | ⟨z,hz⟩)
    · exact ⟨algebraMap K (QuadraticAlgebra K a 0) z, by simp [hz]⟩
    · refine ⟨⟨0,z/a⟩, ?_⟩
      ext
      · simp
        field_simp
        linear_combination hz
      · simp

lemma biquadratic_square_iff {K : Type*} [Field K] [CharZero K]
    (a b d : K) (ha : ¬ IsSquare a) (hb : b ≠ 0) :
    IsSquare
      (algebraMap (QuadraticAlgebra K a 0)
        (QuadraticAlgebra (QuadraticAlgebra K a 0)
          (algebraMap K (QuadraticAlgebra K a 0) b) 0)
        (algebraMap K (QuadraticAlgebra K a 0) d)) ↔
      IsSquare d ∨ IsSquare (a*d) ∨ IsSquare (b*d) ∨ IsSquare (a*(b*d)) := by
  letI : Fact (∀ r : K, r^2 ≠ a+0*r) := ⟨by
    intro r hr
    apply ha
    exact ⟨r, by simpa [pow_two] using hr.symm⟩⟩
  have ha0 : a ≠ 0 := by
    intro h
    exact ha ⟨0, by simp [h]⟩
  have hb0 : algebraMap K (QuadraticAlgebra K a 0) b ≠ 0 := by
    intro h
    have hh := congrArg QuadraticAlgebra.re h
    exact hb (by simpa using hh)
  rw [quadratic_square_iff _ _ hb0, ← map_mul,
    quadratic_square_iff a d ha0, quadratic_square_iff a (b*d) ha0]
  tauto

lemma squarefree_dvd_of_square_mul {K : Type*} [Field K]
    {D Q : K[X]} (hD : Squarefree D) (h : IsSquare (D*Q)) : D ∣ Q := by
  obtain ⟨p,hp⟩ := h
  have hd : D ∣ p^2 := by
    rw [pow_two, ← hp]
    exact dvd_mul_right D Q
  obtain ⟨r,hr⟩ := (hD.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hd
  refine ⟨r*r, ?_⟩
  apply mul_left_cancel₀ hD.ne_zero
  rw [hp, hr]
  ring


lemma isSquare_ratFunc_iff {K : Type*} [Field K] (p : K[X]) :
    IsSquare (algebraMap K[X] (RatFunc K) p) ↔ IsSquare p := by
  constructor
  · rintro ⟨r, hr⟩
    have hint : IsIntegral K[X] (r^2) := by
      rw [pow_two, ← hr]
      exact isIntegral_algebraMap
    obtain ⟨q,hq⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := K[X]) (K := RatFunc K) (by norm_num : 0 < (2 : ℕ)) hint
    refine ⟨q, ?_⟩
    apply IsFractionRing.injective K[X] (RatFunc K)
    simpa [map_mul, hq] using hr
  · rintro ⟨q,hq⟩
    exact ⟨algebraMap K[X] (RatFunc K) q, by simp [hq]⟩

def extra (A B : ℚ) : ℚ[X] :=
  C (A^4-A^2+1)*X^4 + C (4*A^3*B-2*A*B)*X^3 +
    C (6*A^2*B^2-A^2-B^2-1)*X^2 + C (4*A*B^3-2*A*B)*X + C (B^4-B^2+1)

def medianOne (A B : ℚ) : ℚ[X] :=
  C (2-A^2)*X^2+C (-2*A*B)*X+C (2-B^2)

def medianTwo (A B : ℚ) : ℚ[X] :=
  C (-1+2*A^2)*X^2+C (4*A*B)*X+C (2+2*B^2)

private def bezoutU (A B : ℚ) : ℚ[X] :=
  C (32*B^12 - 160*B^10 + 424*B^8 - 162*B^6 - 440*B^4 + 408*B^2 - 96) +
    C (64*A*B^11 - 232*A*B^9 + 600*A*B^7 - 852*A*B^5 + 576*A*B^3 - 144*A*B)*X +
    C (64*B^12 - 160*B^10 + 144*B^8 - 48*B^6)*X^2

private def bezoutV (A B : ℚ) : ℚ[X] :=
  C (-4*A*B^11 + 20*A*B^9 - 56*A*B^7 + 33*A*B^5 + 16*A*B^3 - 12*A*B) +
    C (-24*B^12 + 100*B^10 - 252*B^8 + 219*B^6 + 14*B^4 - 84*B^2 + 24)*X +
    C (-24*A*B^11 + 72*A*B^9 - 156*A*B^7 + 213*A*B^5 - 144*A*B^3 + 36*A*B)*X^2 +
    C (-16*B^12 + 40*B^10 - 36*B^8 + 12*B^6)*X^3

private def bezoutRemainder (A B : ℚ) : ℚ[X] :=
  C (-16*B^14 + 88*B^12 - 264*B^10 + 244*B^8 - 2*B^6 - 80*B^4 + 24*B^2) +
    C (-48*A*B^13 + 248*A*B^11 - 712*A*B^9 + 508*A*B^7 + 126*A*B^5 - 176*A*B^3 + 24*A*B)*X +
    C (-48*A^2*B^12 - 32*B^14 + 240*A^2*B^10 + 88*B^12 - 672*A^2*B^8 - 128*B^10 + 396*A^2*B^6 + 92*B^8 + 192*A^2*B^4 + 48*B^6 - 144*A^2*B^2 - 20*B^4 - 96*B^2 + 48)*X^2 +
    C (-16*A^3*B^11 - 96*A*B^13 + 80*A^3*B^9 + 208*A*B^11 - 224*A^3*B^7 - 120*A*B^9 + 132*A^3*B^5 - 152*A*B^7 + 64*A^3*B^3 + 426*A*B^5 - 48*A^3*B - 320*A*B^3 + 72*A*B)*X^3 +
    C (-96*A^2*B^12 + 176*A^2*B^10 + 16*B^12 - 56*A^2*B^8 + 16*B^10 - 138*A^2*B^6 - 116*B^8 + 192*A^2*B^4 + 258*B^6 - 72*A^2*B^2 - 240*B^4 + 72*B^2)*X^4 +
    C (-32*A^3*B^11 + 56*A^3*B^9 + 16*A*B^11 - 24*A^3*B^7 - 16*A*B^9)*X^5

private def bezoutConstant (B : ℚ) : ℚ :=
  6*(B^2-1)*(B^4-8*B^2+4)^2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private lemma bezout_identity (A B : ℚ) :
    bezoutU A B*extra A B + bezoutV A B*(extra A B).derivative =
      C (bezoutConstant B) + C (A^2-2*B^2+1)*bezoutRemainder A B := by
  simp only [bezoutU, bezoutV, extra, bezoutConstant, bezoutRemainder]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_C]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_neg]
  norm_num
  simp only [Polynomial.C_ofNat]
  ring

private lemma bezoutConstant_ne_zero (B : ℚ) (hB : B^2 ≠ 1) : bezoutConstant B ≠ 0 := by
  have hh : B^4-8*B^2+4 ≠ 0 := by
    intro he
    have hsq : IsSquare (3 : ℚ) := ⟨(B^2-4)/2, by nlinarith [he]⟩
    norm_num at hsq
  exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hB)) (pow_ne_zero _ hh)

lemma extra_squarefree {A B : ℚ} (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    Squarefree (extra A B) := by
  have he := bezout_identity A B
  have hz : A^2-2*B^2+1 = 0 := by linarith
  rw [hz, map_zero, zero_mul, add_zero] at he
  have hconst := bezoutConstant_ne_zero B hB
  apply Polynomial.Separable.squarefree
  rw [separable_def']
  refine ⟨C ((bezoutConstant B)⁻¹)*bezoutU A B,
    C ((bezoutConstant B)⁻¹)*bezoutV A B, ?_⟩
  calc
    _ = C ((bezoutConstant B)⁻¹)*
        (bezoutU A B*extra A B + bezoutV A B*(extra A B).derivative) := by ring
    _ = 1 := by rw [he, ← map_mul, inv_mul_cancel₀ hconst, map_one]


lemma extra_eval (A B : ℚ) (x : ℝ) :
    (extra A B).eval₂ (Rat.castHom ℝ) x =
      x^4+1+((A : ℝ)*x+B)^4-x^2-x^2*((A : ℝ)*x+B)^2-((A : ℝ)*x+B)^2 := by
  simp [extra, eval₂_pow]
  ring

lemma medianOne_eval (A B : ℚ) (x : ℝ) :
    (medianOne A B).eval₂ (Rat.castHom ℝ) x = 2*x^2+2-((A : ℝ)*x+B)^2 := by
  simp [medianOne, eval₂_pow]
  ring

lemma medianTwo_eval (A B : ℚ) (x : ℝ) :
    (medianTwo A B).eval₂ (Rat.castHom ℝ) x = -x^2+2+2*((A : ℝ)*x+B)^2 := by
  simp [medianTwo, eval₂_pow]
  ring

private lemma rational_sq_ne_three (q : ℚ) : (q : ℝ)^2 ≠ 3 := by
  intro h
  have hq : q^2 = 3 := by exact_mod_cast h
  have hs : IsSquare (3 : ℚ) := ⟨q, by nlinarith [hq]⟩
  norm_num at hs

lemma extra_positive {A B : ℚ} (hAB : A^2 = 2*B^2-1) (x : ℝ) :
    0 < (extra A B).eval₂ (Rat.castHom ℝ) x := by
  rw [extra_eval]
  have hR : (A : ℝ)^2 = 2*(B : ℝ)^2-1 := by exact_mod_cast hAB
  have hmed : (2*(B : ℝ)*x+A)^2 = 2*x^2-1+2*((A : ℝ)*x+B)^2 := by
    linear_combination (1-2*x^2)*hR
  by_contra hn
  push_neg at hn
  have hx : x^2 = 1 := by
    nlinarith [sq_nonneg (x^2-1), sq_nonneg (((A : ℝ)*x+B)^2-1),
      sq_nonneg (x^2-((A : ℝ)*x+B)^2)]
  have hc : ((A : ℝ)*x+B)^2 = 1 := by
    nlinarith [sq_nonneg (x^2-1), sq_nonneg (((A : ℝ)*x+B)^2-1),
      sq_nonneg (x^2-((A : ℝ)*x+B)^2)]
  have hv : (2*(B : ℝ)*x+A)^2 = 3 := by nlinarith [hmed]
  rcases sq_eq_one_iff.mp hx with hx | hx
  · subst x
    apply rational_sq_ne_three (2*B+A)
    push_cast
    simpa using hv
  · subst x
    apply rational_sq_ne_three (-2*B+A)
    push_cast
    convert hv using 1; ring

lemma extra_natDegree (A B : ℚ) : (extra A B).natDegree = 4 := by
  have hle : (extra A B).natDegree ≤ 4 := by unfold extra; compute_degree!
  apply le_antisymm hle
  apply le_natDegree_of_ne_zero
  have hn : A^4-A^2+1 ≠ 0 := by nlinarith [sq_nonneg (A^2-1/2)]
  simp only [extra, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num
  exact hn

lemma medianOne_natDegree_le (A B : ℚ) : (medianOne A B).natDegree ≤ 2 := by
  unfold medianOne
  compute_degree!

lemma medianTwo_natDegree_le (A B : ℚ) : (medianTwo A B).natDegree ≤ 2 := by
  unfold medianTwo
  compute_degree!

lemma medianTwo_ne_zero (A B : ℚ) : medianTwo A B ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval 0) h
  simp [medianTwo] at he
  nlinarith [sq_nonneg B]

lemma exists_negative_median_product {A B : ℚ}
    (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    ∃ x : ℝ, (medianOne A B).eval₂ (Rat.castHom ℝ) x *
      (medianTwo A B).eval₂ (Rat.castHom ℝ) x < 0 := by
  have hR : (A : ℝ)^2 = 2*(B : ℝ)^2-1 := by exact_mod_cast hAB
  by_contra hh
  push_neg at hh
  have hboth (x : ℝ) : 0 ≤ 2*x^2+2-((A : ℝ)*x+B)^2 ∧
      0 ≤ -x^2+2+2*((A : ℝ)*x+B)^2 := by
    have hm := hh x
    rw [medianOne_eval, medianTwo_eval] at hm
    have hs : 0 < (2*x^2+2-((A : ℝ)*x+B)^2)+(-x^2+2+2*((A : ℝ)*x+B)^2) := by
      nlinarith [sq_nonneg x, sq_nonneg ((A : ℝ)*x+B)]
    constructor <;> nlinarith [sq_nonneg (2*x^2+2-((A : ℝ)*x+B)^2),
      sq_nonneg (-x^2+2+2*((A : ℝ)*x+B)^2)]
  have h1 := discrim_le_zero (a := 2-(A : ℝ)^2) (b := -2*(A : ℝ)*B)
    (c := 2-(B : ℝ)^2) (fun x => by convert (hboth x).1 using 1; ring)
  have h2 := discrim_le_zero (a := -1+2*(A : ℝ)^2) (b := 4*(A : ℝ)*B)
    (c := 2+2*(B : ℝ)^2) (fun x => by convert (hboth x).2 using 1; ring)
  have he1 : discrim (2-(A : ℝ)^2) (-2*(A : ℝ)*B) (2-(B : ℝ)^2) =
      24*((B : ℝ)^2-1) := by
    unfold discrim
    linear_combination 8*hR
  have he2 : discrim (-1+2*(A : ℝ)^2) (4*(A : ℝ)*B) (2+2*(B : ℝ)^2) =
      -24*((B : ℝ)^2-1) := by
    unfold discrim
    linear_combination -16*hR
  rw [he1] at h1
  rw [he2] at h2
  have he : (B : ℝ)^2 = 1 := by linarith
  exact hB (by exact_mod_cast he)


private lemma discr_zero_of_square_quadratic (a b c : ℚ)
    (h : IsSquare (C a*X^2+C b*X+C c)) : b^2-4*a*c = 0 := by
  obtain ⟨p,hp⟩ := h
  have hdeg : (C a*X^2+C b*X+C c).natDegree ≤ 2 := by compute_degree!
  have hpdeg : p.natDegree ≤ 1 := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [hp, natDegree_mul hp0 hp0] at hdeg
      omega
  obtain ⟨r,s,hrs⟩ := exists_eq_X_add_C_of_natDegree_le_one hpdeg
  have he : C a*X^2+C b*X+C c = C (r*r)*X^2+C (2*r*s)*X+C (s*s) := by
    rw [hp, hrs]
    simp only [map_mul, map_ofNat]
    ring
  have ha := congrArg (fun f : ℚ[X] => f.coeff 2) he
  have hb := congrArg (fun f : ℚ[X] => f.coeff 1) he
  have hc := congrArg (fun f : ℚ[X] => f.coeff 0) he
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at ha hb hc
  norm_num at ha hb hc
  rw [ha, hb, hc]
  ring

lemma medianOne_not_square {A B : ℚ} (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    ¬ IsSquare (medianOne A B) := by
  intro h
  have hh := discr_zero_of_square_quadratic _ _ _ h
  exact hB (by nlinarith [hh, hAB])

lemma medianOne_ne_zero {A B : ℚ} (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    medianOne A B ≠ 0 := by
  intro h
  apply medianOne_not_square hAB hB
  exact ⟨0, by simp [h]⟩

private lemma not_square_mul_of_degree_lt {D Q : ℚ[X]} (hD : Squarefree D)
    (hQ : Q ≠ 0) (hdeg : Q.natDegree < D.natDegree) : ¬ IsSquare (D*Q) := by
  intro h
  exact (not_le_of_gt hdeg) (natDegree_le_of_dvd (squarefree_dvd_of_square_mul hD h) hQ)

lemma no_polynomial_square_classes {A B : ℚ}
    (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    ¬ IsSquare (extra A B) ∧
    ¬ IsSquare (medianOne A B*extra A B) ∧
    ¬ IsSquare (medianTwo A B*extra A B) ∧
    ¬ IsSquare (medianOne A B*(medianTwo A B*extra A B)) := by
  have hsf := extra_squarefree hAB hB
  have hd := extra_natDegree A B
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using not_square_mul_of_degree_lt (Q := 1) hsf one_ne_zero (by simp [hd])
  · simpa only [mul_comm] using not_square_mul_of_degree_lt hsf
      (medianOne_ne_zero hAB hB) (by have := medianOne_natDegree_le A B; omega)
  · simpa only [mul_comm] using not_square_mul_of_degree_lt hsf
      (medianTwo_ne_zero A B) (by have := medianTwo_natDegree_le A B; omega)
  · rintro ⟨p,hp⟩
    obtain ⟨x,hx⟩ := exists_negative_median_product hAB hB
    have hpos := extra_positive hAB x
    have hneg : (medianOne A B).eval₂ (Rat.castHom ℝ) x *
        ((medianTwo A B).eval₂ (Rat.castHom ℝ) x *
          (extra A B).eval₂ (Rat.castHom ℝ) x) < 0 := by
      rw [← mul_assoc]
      exact mul_neg_of_neg_of_pos hx hpos
    have he := congrArg (Polynomial.eval₂ (Rat.castHom ℝ) x) hp
    simp only [eval₂_mul] at he
    rw [he] at hneg
    exact (not_lt_of_ge (mul_self_nonneg _)) hneg

lemma no_rationalFunction_square_classes {A B : ℚ}
    (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    let a := algebraMap ℚ[X] (RatFunc ℚ) (medianOne A B)
    let b := algebraMap ℚ[X] (RatFunc ℚ) (medianTwo A B)
    let d := algebraMap ℚ[X] (RatFunc ℚ) (extra A B)
    ¬ IsSquare d ∧ ¬ IsSquare (a*d) ∧ ¬ IsSquare (b*d) ∧ ¬ IsSquare (a*(b*d)) := by
  dsimp only
  simp only [← map_mul, isSquare_ratFunc_iff]
  exact no_polynomial_square_classes hAB hB

/-- The eighth-template square condition is not automatic on any
nondegenerate fiber of this rational-median fibration. This statement is about
its function field; it does not rule out individual rational parameter values. -/
theorem no_automatic_extra_square {A B : ℚ}
    (hAB : A^2 = 2*B^2-1) (hB : B^2 ≠ 1) :
    let a := algebraMap ℚ[X] (RatFunc ℚ) (medianOne A B)
    let b := algebraMap ℚ[X] (RatFunc ℚ) (medianTwo A B)
    let d := algebraMap ℚ[X] (RatFunc ℚ) (extra A B)
    let L := QuadraticAlgebra (RatFunc ℚ) a 0
    ¬ IsSquare (algebraMap L
      (QuadraticAlgebra L (algebraMap (RatFunc ℚ) L b) 0)
      (algebraMap (RatFunc ℚ) L d)) := by
  dsimp only
  have ha : ¬ IsSquare (algebraMap ℚ[X] (RatFunc ℚ) (medianOne A B)) := by
    rw [isSquare_ratFunc_iff]
    exact medianOne_not_square hAB hB
  have hb : algebraMap ℚ[X] (RatFunc ℚ) (medianTwo A B) ≠ 0 := by
    intro hh
    apply medianTwo_ne_zero A B
    apply RatFunc.algebraMap_injective ℚ
    rw [map_zero]
    exact hh
  rw [biquadratic_square_iff _ _ _ ha hb]
  have hh := no_rationalFunction_square_classes hAB hB
  dsimp only at hh
  tauto


def rulingA (k : ℚ) : ℚ := (k^2+4*k+2)/(k^2-2)
def rulingB (k : ℚ) : ℚ := -(k^2+2*k+2)/(k^2-2)

private lemma ruling_den_ne_zero (k : ℚ) : k^2-2 ≠ 0 := by
  intro h
  have hs : IsSquare (2 : ℚ) := ⟨k, by nlinarith [h]⟩
  norm_num at hs

lemma ruling_relation (k : ℚ) : (rulingA k)^2 = 2*(rulingB k)^2-1 := by
  unfold rulingA rulingB
  field_simp [ruling_den_ne_zero k]
  ring

lemma ruling_degenerate_iff (k : ℚ) :
    (rulingB k)^2 = 1 ↔ k = 0 ∨ k = -1 ∨ k = -2 := by
  have he : ((rulingB k)^2-1)*(k^2-2)^2 = 4*k*(k+1)*(k+2) := by
    unfold rulingB
    field_simp [ruling_den_ne_zero k]
    ring
  constructor
  · intro hh
    rw [hh] at he
    norm_num at he
    rcases he with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num [rulingB]

lemma ruling_nondegenerate {k : ℚ} (h0 : k ≠ 0) (h1 : k ≠ -1) (h2 : k ≠ -2) :
    (rulingB k)^2 ≠ 1 := by
  intro h
  have hh := (ruling_degenerate_iff k).mp h
  tauto

lemma ruling_median_identity (k a : ℚ) :
    (2*rulingB k*a+rulingA k)^2 = 2*a^2-1+2*(rulingA k*a+rulingB k)^2 := by
  linear_combination (1-2*a^2)*(ruling_relation k)

#print axioms ruling_relation
#print axioms ruling_nondegenerate

#print axioms no_automatic_extra_square
#print axioms extra_positive
#print axioms exists_negative_median_product

#print axioms extra_squarefree

end
end Erdos213.MedianFibration
