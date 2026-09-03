import FormalConjecturesUtil

/-! Algebraic certificates for the genus-three approach to the eight-point
norm template. No existence or nonexistence theorem is claimed here. -/

set_option linter.unnecessarySeqFocus false

namespace Erdos213.GenusThreeCurve

open Polynomial
open scoped QuadraticAlgebra
noncomputable section

def f (z : ℚ) : ℚ := z*(z^2-1)*(z^2-9)*(z^2+3)

def branchPolynomial : ℚ[X] := X*(X^2-1)*(X^2-9)*(X^2+3)

def quadratic (b c : ℚ) : ℚ[X] := X^2 + C b*X + C c

lemma involution_identity {z : ℚ} (hz : z ≠ 0) :
    f (3/z) = 81*f z/z^8 := by
  dsimp [f]
  field_simp
  ring_nf

lemma degree_two_identity {z : ℚ} (hz : z ≠ 0) :
    f z = z^4*((z+3/z)^3-16*(z+3/z)) := by
  dsimp [f]
  field_simp
  ring_nf

lemma degree_two_quotient {z y δ : ℚ} (hz : z ≠ 0) (hy : y^2 = δ*f z) :
    (y/z^2)^2 = δ*((z+3/z)^3-16*(z+3/z)) := by
  rw [div_pow, hy, degree_two_identity hz]
  field_simp

lemma degree_three_identity {z : ℚ} (hz : z^2-1 ≠ 0) :
    f z*(z^2+3)^2 = (z^2-1)^4 *
      ((z*(z^2-9)/(z^2-1))^3+27*(z*(z^2-9)/(z^2-1))) := by
  dsimp [f]
  field_simp
  ring_nf

lemma degree_three_quotient {z y δ : ℚ} (hz : z^2-1 ≠ 0) (hy : y^2 = δ*f z) :
    (y*(z^2+3)/(z^2-1)^2)^2 =
      δ*((z*(z^2-9)/(z^2-1))^3+27*(z*(z^2-9)/(z^2-1))) := by
  have he := degree_three_identity hz
  rw [div_pow, mul_pow, hy]
  calc
    δ*f z*(z^2+3)^2 / ((z^2-1)^2)^2 = δ*(f z*(z^2+3)^2)/(z^2-1)^4 := by ring_nf
    _ = _ := by rw [he]; field_simp

private lemma isSquare_of_square_ratio {a b c : ℚ} (hb : b ≠ 0)
    (h : a^2 = b^2*c) : IsSquare c := by
  refine ⟨a/b, ?_⟩
  field_simp
  nlinarith [h]

/-- A polynomial Pell-type certificate gives square values at every real
branch point where its denominator does not vanish. -/
lemma pell_branch_square (V W : ℚ[X]) (δ b c r : ℚ)
    (h : V^2-C δ*branchPolynomial = W^2*quadratic b c)
    (hr : f r = 0) (hW : W.eval r ≠ 0) : IsSquare (r^2+b*r+c) := by
  have he := congrArg (Polynomial.eval r) h
  dsimp [f] at hr
  simp [branchPolynomial, quadratic] at he
  rw [hr] at he
  simp only [mul_zero, sub_zero] at he
  exact isSquare_of_square_ratio hW he

abbrev RootAlgebra := QuadraticAlgebra ℚ (-3) 0

noncomputable def rootEval : ℚ[X] →+* RootAlgebra :=
  Polynomial.eval₂RingHom (algebraMap ℚ RootAlgebra) QuadraticAlgebra.omega

private lemma rootEval_branch : rootEval branchPolynomial = 0 := by
  have hω : (QuadraticAlgebra.omega : RootAlgebra)^2 + 3 = 0 := by
    ext <;> norm_num [pow_two, QuadraticAlgebra.omega]
  have hx : rootEval X = QuadraticAlgebra.omega := by simp [rootEval]
  simp only [branchPolynomial, map_mul, map_add, map_sub, map_pow,
    map_one, map_ofNat, hx]
  rw [hω, mul_zero]

private lemma rootEval_quadratic (b c : ℚ) :
    rootEval (quadratic b c) = ⟨c-3,b⟩ := by
  ext <;> simp [rootEval, quadratic, Polynomial.eval₂RingHom,
    pow_two, QuadraticAlgebra.omega] <;> ring_nf

private lemma rootNorm_quadratic (b c : ℚ) :
    QuadraticAlgebra.norm (rootEval (quadratic b c)) = (c-3)^2+3*b^2 := by
  rw [rootEval_quadratic, QuadraticAlgebra.norm_def]
  ring_nf

/-- The same polynomial certificate gives the sixth square condition by taking
norms in `ℚ(√-3)`. This is an exact certificate, not an assertion that suitable
polynomials exist. -/
lemma pell_extra_square (V W : ℚ[X]) (δ b c : ℚ)
    (h : V^2-C δ*branchPolynomial = W^2*quadratic b c)
    (hW : QuadraticAlgebra.norm (rootEval W) ≠ 0) :
    IsSquare ((c-3)^2+3*b^2) := by
  have he := congrArg rootEval h
  simp only [map_sub, map_mul, map_pow, rootEval_branch, mul_zero, sub_zero] at he
  have hn := congrArg QuadraticAlgebra.norm he
  simp only [map_pow, map_mul, rootNorm_quadratic] at hn
  exact isSquare_of_square_ratio hW hn

/-- The six arithmetic norm conditions used by the conditional template. -/
def SquareConditions (b c : ℚ) : Prop :=
  IsSquare c ∧ IsSquare (1+b+c) ∧ IsSquare (1-b+c) ∧
    IsSquare (9+3*b+c) ∧ IsSquare (9-3*b+c) ∧ IsSquare ((c-3)^2+3*b^2)

lemma pell_square_conditions (V W : ℚ[X]) (δ b c : ℚ)
    (h : V^2-C δ*branchPolynomial = W^2*quadratic b c)
    (hW : ∀ r ∈ ({0,1,-1,3,-3} : Set ℚ), W.eval r ≠ 0)
    (hWq : QuadraticAlgebra.norm (rootEval W) ≠ 0) : SquareConditions b c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, pell_extra_square V W δ b c h hWq⟩
  · simpa using pell_branch_square V W δ b c 0 h (by norm_num [f]) (hW 0 (by simp))
  · simpa using pell_branch_square V W δ b c 1 h (by norm_num [f]) (hW 1 (by simp))
  · simpa [sub_eq_add_neg] using pell_branch_square V W δ b c (-1) h
      (by norm_num [f]) (hW (-1) (by simp))
  · convert pell_branch_square V W δ b c 3 h (by norm_num [f]) (hW 3 (by simp)) using 1 <;> ring_nf
  · convert pell_branch_square V W δ b c (-3) h (by norm_num [f]) (hW (-3) (by simp)) using 1 <;> ring_nf

lemma square_conditions_not_c_three {b c : ℚ} (h : SquareConditions b c) : c ≠ 3 := by
  rintro rfl
  have hh := h.1
  norm_num at hh

/-- A complex number of rational Euclidean norm. -/
def RationalNorm (z : ℂ) : Prop := ∃ q : ℚ, (q : ℝ) = ‖z‖

lemma rationalNorm_iff_isSquare {z : ℂ} {r : ℚ}
    (hr : Complex.normSq z = (r : ℝ)) : RationalNorm z ↔ IsSquare r := by
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q, ?_⟩
    have hh : (r : ℝ) = (q : ℝ)^2 := by rw [← hr, Complex.normSq_eq_norm_sq, ← hq]
    exact_mod_cast (hh.trans (pow_two (q : ℝ)))
  · rintro ⟨q,hq⟩
    refine ⟨|q|, ?_⟩
    rw [Rat.cast_abs]
    apply (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs, ← Complex.normSq_eq_norm_sq, hr, hq]
    push_cast
    ring_nf

lemma normSq_shift (z : ℂ) {b c : ℚ} (hc : Complex.normSq z = (c : ℝ))
    (hb : 2*z.re = -(b : ℝ)) (r : ℚ) :
    Complex.normSq (z-(r : ℂ)) = ((r^2+b*r+c : ℚ) : ℝ) := by
  simp only [Complex.normSq_apply] at hc ⊢
  simp only [Complex.sub_re, Complex.sub_im, Complex.ratCast_re, Complex.ratCast_im,
    sub_zero]
  push_cast
  linear_combination hc - (r : ℝ)*hb

lemma normSq_extra (z : ℂ) :
    Complex.normSq (z^2+3) = (Complex.normSq z-3)^2+12*z.re^2 := by
  simp only [Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  ring_nf

lemma square_conditions_iff_norms (z : ℂ) {b c : ℚ}
    (hc : Complex.normSq z = (c : ℝ)) (hb : 2*z.re = -(b : ℝ)) :
    SquareConditions b c ↔
      RationalNorm z ∧ RationalNorm (z-1) ∧ RationalNorm (z+1) ∧
      RationalNorm (z-3) ∧ RationalNorm (z+3) ∧ RationalNorm (z^2+3) := by
  have h1 : Complex.normSq (z-1) = ((1+b+c : ℚ) : ℝ) := by
    simpa using normSq_shift z hc hb 1
  have hm1 : Complex.normSq (z+1) = ((1-b+c : ℚ) : ℝ) := by
    simpa [sub_eq_add_neg] using normSq_shift z hc hb (-1)
  have h3 : Complex.normSq (z-3) = ((9+3*b+c : ℚ) : ℝ) := by
    convert normSq_shift z hc hb 3 using 1 <;> push_cast <;> ring_nf
  have hm3 : Complex.normSq (z+3) = ((9-3*b+c : ℚ) : ℝ) := by
    convert normSq_shift z hc hb (-3) using 1 <;> push_cast <;> ring_nf
  have hq : Complex.normSq (z^2+3) = (((c-3)^2+3*b^2 : ℚ) : ℝ) := by
    have hre : z.re = -(b : ℝ)/2 := by linarith
    rw [normSq_extra, hc, hre]
    push_cast
    ring_nf
  rw [rationalNorm_iff_isSquare hc, rationalNorm_iff_isSquare h1,
    rationalNorm_iff_isSquare hm1, rationalNorm_iff_isSquare h3,
    rationalNorm_iff_isSquare hm3, rationalNorm_iff_isSquare hq]
  rfl

lemma exists_nonreal_parameter {b c : ℚ} (h : 0 < 4*c-b^2) :
    ∃ z : ℂ, z.im ≠ 0 ∧ Complex.normSq z = (c : ℝ) ∧ 2*z.re = -(b : ℝ) := by
  have hr : (0 : ℝ) < 4*(c : ℝ)-(b : ℝ)^2 := by exact_mod_cast h
  refine ⟨⟨-(b : ℝ)/2, Real.sqrt (4*(c : ℝ)-(b : ℝ)^2)/2⟩, ?_, ?_, ?_⟩
  · exact ne_of_gt (div_pos (Real.sqrt_pos.mpr hr) (by norm_num))
  · rw [Complex.normSq_apply]
    dsimp
    nlinarith [Real.sq_sqrt hr.le]
  · dsimp
    ring_nf

lemma RationalNorm.div {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z/w) := by
  obtain ⟨a,ha⟩ := hz
  obtain ⟨b,hb⟩ := hw
  exact ⟨a/b, by simp [ha, hb]⟩

/-- The six square conditions and negative discriminant give precisely the
nonreal norm parameter required by the existing conditional eight-point
construction. They do not by themselves assert general position. -/
lemma exists_template_parameter {b c : ℚ}
    (hdisc : 0 < 4*c-b^2) (hsq : SquareConditions b c) :
    ∃ t : ℂ, t.im ≠ 0 ∧ RationalNorm t ∧ RationalNorm (t+1) ∧
      RationalNorm (t-1) ∧ RationalNorm (t+2) ∧ RationalNorm (2*t+1) ∧
      RationalNorm (t^2+t+1) := by
  obtain ⟨z,hz,hc,hb⟩ := exists_nonreal_parameter hdisc
  obtain ⟨hn,hn1,hnm1,hn3,hnm3,hnq⟩ := (square_conditions_iff_norms z hc hb).mp hsq
  have h2 : RationalNorm (2 : ℂ) := ⟨2, by norm_num⟩
  have h4 : RationalNorm (4 : ℂ) := ⟨4, by norm_num⟩
  let t : ℂ := (z-1)/2
  have ht : 2*t+1 = z := by dsimp [t]; ring_nf
  refine ⟨t, ?_, hn1.div h2, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hh := congrArg Complex.im ht
    simp [hzero] at hh
    exact hz hh.symm
  · have he : t+1 = (z+1)/2 := by dsimp [t]; ring_nf
    rw [he]
    exact hnm1.div h2
  · have he : t-1 = (z-3)/2 := by dsimp [t]; ring_nf
    rw [he]
    exact hn3.div h2
  · have he : t+2 = (z+3)/2 := by dsimp [t]; ring_nf
    rw [he]
    exact hnm3.div h2
  · rw [ht]
    exact hn
  · have he : t^2+t+1 = (z^2+3)/4 := by dsimp [t]; ring_nf
    rw [he]
    exact hnq.div h4

#print axioms exists_template_parameter
#print axioms square_conditions_iff_norms
#print axioms exists_nonreal_parameter
#print axioms degree_two_quotient
#print axioms degree_three_quotient
#print axioms pell_square_conditions

end
end Erdos213.GenusThreeCurve
