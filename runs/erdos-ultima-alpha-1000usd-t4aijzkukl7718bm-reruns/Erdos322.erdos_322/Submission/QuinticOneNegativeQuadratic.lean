import FormalConjecturesUtil

/-! A quadratic polynomial constant-sum identity for fifth powers cannot
pass through a nonnegative point when exactly one leading coefficient is
negative and its coordinate is positive. No representation-count bound is
asserted. The number of other coordinates is unrestricted. -/
namespace Erdos322Research.QuinticOneNegativeQuadratic
noncomputable section
open Polynomial Finset
set_option Elab.async false

private def quadratic (a b c : ℝ) : ℝ[X] := C a*X^2+C b*X+C c

private lemma top_coefficients (a b c : ℝ) :
    (quadratic a b c^5).coeff 10=a^5 ∧
    (quadratic a b c^5).coeff 9=5*a^4*b ∧
    (quadratic a b c^5).coeff 8=5*a^4*c+10*a^3*b^2 := by
  have he : quadratic a b c^5 =
      C (a^5)*X^10+C (5*a^4*b)*X^9+C (5*a^4*c+10*a^3*b^2)*X^8+
      C (20*a^3*b*c+10*a^2*b^3)*X^7+
      C (10*a^3*c^2+30*a^2*b^2*c+5*a*b^4)*X^6+
      C (30*a^2*b*c^2+20*a*b^3*c+b^5)*X^5+
      C (10*a^2*c^3+30*a*b^2*c^2+5*b^4*c)*X^4+
      C (20*a*b*c^3+10*b^3*c^2)*X^3+
      C (5*a*c^4+10*b^2*c^3)*X^2+C (5*b*c^4)*X+C (c^5) := by
    simp only [quadratic,map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  norm_num

private lemma coefficient_relations {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (A B D N : ℝ)
    (h : (∑ i, quadratic (a i) (b i) (c i)^5)+quadratic (-A) B D^5=C N) :
    (∑ i, a i^5)=A^5 ∧ (∑ i, a i^4*b i) = -A^4*B ∧
    (∑ i, a i^4*c i)+2*(∑ i, a i^3*b i^2)+A^4*D-2*A^3*B^2=0 := by
  have h10 := congrArg (fun p : ℝ[X] ↦ p.coeff 10) h
  have h9 := congrArg (fun p : ℝ[X] ↦ p.coeff 9) h
  have h8 := congrArg (fun p : ℝ[X] ↦ p.coeff 8) h
  simp only [coeff_add,finset_sum_coeff,(top_coefficients _ _ _).1,coeff_C,
    OfNat.ofNat_ne_zero,ite_false] at h10
  simp only [coeff_add,finset_sum_coeff,(top_coefficients _ _ _).2.1,coeff_C,
    OfNat.ofNat_ne_zero,ite_false] at h9
  simp only [coeff_add,finset_sum_coeff,(top_coefficients _ _ _).2.2,coeff_C,
    OfNat.ofNat_ne_zero,ite_false] at h8
  have hs9 : (∑ i, 5*a i^4*b i)=5*(∑ i, a i^4*b i) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have hs8 : (∑ i, (5*a i^4*c i+10*a i^3*b i^2))=
      5*(∑ i, a i^4*c i)+10*(∑ i, a i^3*b i^2) := by
    simp only [sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring
  rw [hs9] at h9
  rw [hs8] at h8
  constructor
  · nlinarith only [h10]
  constructor
  · nlinarith only [h9]
  · nlinarith only [h8]

/-- The top three coefficients and weighted Cauchy--Schwarz imply this
inequality at EVERY parameter, without any sign hypothesis on the values. -/
theorem weighted_value_nonpositive {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (A B D N : ℝ) (ha : ∀ i, 0 ≤ a i) (hA : 0 < A)
    (h : (∑ i, (C (a i)*X^2+C (b i)*X+C (c i))^5)+
      (C (-A)*X^2+C B*X+C D)^5=C N) (t : ℝ) :
    (∑ i, a i^4*(a i*t^2+b i*t+c i))+A^4*(-A*t^2+B*t+D) ≤ 0 := by
  obtain ⟨h5,h4,h3⟩ := coefficient_relations a b c A B D N h
  have hCS : (∑ i, a i^4*b i)^2 ≤ (∑ i, a i^5)*(∑ i, a i^3*b i^2) := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ ↦ pow_nonneg (ha i) 5)
      (fun i _ ↦ mul_nonneg (pow_nonneg (ha i) 3) (sq_nonneg _))
      (fun i _ ↦ by ring)
  rw [h5,h4] at hCS
  have hbound : A^3*B^2 ≤ ∑ i, a i^3*b i^2 := by
    refine le_of_mul_le_mul_left (a := A^5) ?_ (pow_pos hA 5)
    nlinarith only [hCS]
  have he : (∑ i, a i^4*(a i*t^2+b i*t+c i))+A^4*(-A*t^2+B*t+D) =
      (∑ i, a i^4*c i)+A^4*D := by
    have hs : (∑ i, a i^4*(a i*t^2+b i*t+c i)) =
        (∑ i, a i^5)*t^2+(∑ i, a i^4*b i)*t+(∑ i, a i^4*c i) := by
      simp only [Finset.sum_mul,← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hs,h5,h4]
    ring
  rw [he]
  linarith only [h3,hbound]

/-- No such quadratic identity has a nonnegative point whose sole
negative-leading coordinate is positive. This includes the Euler leading
vector (27,84,110,133,-144), with arbitrary lower coefficients. -/
theorem no_nonnegative_point {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (A B D N t : ℝ) (ha : ∀ i, 0 ≤ a i) (hA : 0 < A)
    (hp : ∀ i, 0 ≤ a i*t^2+b i*t+c i) (hq : 0 < -A*t^2+B*t+D) :
    (∑ i, (C (a i)*X^2+C (b i)*X+C (c i))^5)+
      (C (-A)*X^2+C B*X+C D)^5 ≠ C N := by
  intro h
  have hn := weighted_value_nonpositive a b c A B D N ha hA h t
  have hs : 0 ≤ ∑ i, a i^4*(a i*t^2+b i*t+c i) :=
    sum_nonneg fun i _ ↦ mul_nonneg (by positivity) (hp i)
  have ht : 0 < A^4*(-A*t^2+B*t+D) := mul_pos (pow_pos hA 4) hq
  linarith

end
end Erdos322Research.QuinticOneNegativeQuadratic
