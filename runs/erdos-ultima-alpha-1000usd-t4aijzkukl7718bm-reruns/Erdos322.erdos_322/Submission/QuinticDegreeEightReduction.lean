import FormalConjecturesUtil

/-! Exact coefficient invariants for a restricted quintic polynomial
construction of degrees (8,8,7,6,5). This does not settle Erdős 322. -/
namespace Erdos322Research.QuinticDegreeEight
noncomputable section
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The weighted-variable form of the degree-eight construction, after
normalizing its fourth coordinate's linear coefficient to one. -/
def model (a A b c d f : ℚ) : ℚ[X] :=
  X^3*((C a+C b*X)^5+(C A-C b*X)^5)+
  X^2*(C c+C d*X)^5+X*(1+C f*X)^5+(1-C (1/5)*X)^5

private def p0 (a A b : ℚ) : ℚ := a^5+A^5
private def p1 (a A b : ℚ) : ℚ := 5*b*(a^4-A^4)
private def p2 (a A b : ℚ) : ℚ := 10*b^2*(a^3+A^3)
private def p3 (a A b : ℚ) : ℚ := 10*b^3*(a^2-A^2)
private def p4 (a A b : ℚ) : ℚ := 5*b^4*(a+A)

def r0 (c d f : ℚ) : ℚ := 2/25-10*f^2-5*c^4*d
def r1 (c d f : ℚ) : ℚ := -1/125-10*f^3-10*c^3*d^2
def r2 (c d f : ℚ) : ℚ := 1/3125-5*f^4-10*c^2*d^3
def r3 (c d f : ℚ) : ℚ := -f^5-5*c*d^4
def r4 (c d f : ℚ) : ℚ := -d^5

/-- The depressed-quartic odd-coefficient invariant. -/
def firstInvariant (r0 r1 r2 r3 r4 : ℚ) : ℚ :=
  8*r1*r4^2-4*r2*r3*r4+r3^3

/-- The depressed-quartic constant-term invariant. -/
def secondInvariant (r0 r1 r2 r3 r4 : ℚ) : ℚ :=
  80*r0*r4^3+r3^4-2*r2*r3^2*r4-4*r2^2*r4^2

private lemma pair_invariants (a A b : ℚ) :
    firstInvariant (p0 a A b) (p1 a A b) (p2 a A b) (p3 a A b) (p4 a A b)=0 ∧
    secondInvariant (p0 a A b) (p1 a A b) (p2 a A b) (p3 a A b) (p4 a A b)=0 := by
  constructor <;> dsimp [firstInvariant,secondInvariant,p0,p1,p2,p3,p4] <;> ring

private lemma coeff2 (a A b c d f : ℚ) :
    (model a A b c d f).coeff 2 = c^5+5*f+2/5 := by
  dsimp [model]
  ring_nf
  simp only [← map_pow,coeff_add,coeff_sub,coeff_neg,coeff_mul_C,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C,coeff_one,coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff3 (a A b c d f : ℚ) :
    (model a A b c d f).coeff 3 = p0 a A b-r0 c d f := by
  dsimp [model,p0,r0]
  ring_nf
  simp only [← map_pow,coeff_add,coeff_sub,coeff_neg,coeff_mul_C,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C,coeff_one,coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff4 (a A b c d f : ℚ) :
    (model a A b c d f).coeff 4 = p1 a A b-r1 c d f := by
  dsimp [model,p1,r1]
  ring_nf
  simp only [← map_pow,coeff_add,coeff_sub,coeff_neg,coeff_mul_C,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C,coeff_one,coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff5 (a A b c d f : ℚ) :
    (model a A b c d f).coeff 5 = p2 a A b-r2 c d f := by
  dsimp [model,p2,r2]
  ring_nf
  simp only [← map_pow,coeff_add,coeff_sub,coeff_neg,coeff_mul_C,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C,coeff_one,coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff6 (a A b c d f : ℚ) :
    (model a A b c d f).coeff 6 = p3 a A b-r3 c d f := by
  dsimp [model,p3,r3]
  ring_nf
  simp only [← map_pow,coeff_add,coeff_sub,coeff_neg,coeff_mul_C,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C,coeff_one,coeff_mul_ofNat]
  norm_num
  ring

private lemma coeff7 (a A b c d f : ℚ) :
    (model a A b c d f).coeff 7 = p4 a A b-r4 c d f := by
  dsimp [model,p4,r4]
  ring_nf
  simp only [← map_pow,coeff_add,coeff_sub,coeff_neg,coeff_mul_C,coeff_C_mul,
    coeff_X_pow,coeff_X,coeff_C,coeff_one,coeff_mul_ofNat]
  norm_num
  ring

/-- Every rational constant identity in this normalized chart satisfies
the two explicit algebraic equations used in the elimination calculation. -/
theorem necessary_equations (a A b c d f : ℚ) (he : model a A b c d f = 1) :
    f=-c^5/5-2/25 ∧
    firstInvariant (r0 c d f) (r1 c d f) (r2 c d f) (r3 c d f) (r4 c d f)=0 ∧
    secondInvariant (r0 c d f) (r1 c d f) (r2 c d f) (r3 c d f) (r4 c d f)=0 := by
  have h2 := congrArg (fun p : ℚ[X] ↦ p.coeff 2) he
  have h3 := congrArg (fun p : ℚ[X] ↦ p.coeff 3) he
  have h4 := congrArg (fun p : ℚ[X] ↦ p.coeff 4) he
  have h5 := congrArg (fun p : ℚ[X] ↦ p.coeff 5) he
  have h6 := congrArg (fun p : ℚ[X] ↦ p.coeff 6) he
  have h7 := congrArg (fun p : ℚ[X] ↦ p.coeff 7) he
  simp only [coeff2,coeff_one,OfNat.ofNat_ne_zero,if_false] at h2
  simp only [coeff3,coeff_one,OfNat.ofNat_ne_zero,if_false,sub_eq_zero] at h3
  simp only [coeff4,coeff_one,OfNat.ofNat_ne_zero,if_false,sub_eq_zero] at h4
  simp only [coeff5,coeff_one,OfNat.ofNat_ne_zero,if_false,sub_eq_zero] at h5
  simp only [coeff6,coeff_one,OfNat.ofNat_ne_zero,if_false,sub_eq_zero] at h6
  simp only [coeff7,coeff_one,OfNat.ofNat_ne_zero,if_false,sub_eq_zero] at h7
  refine ⟨by linarith only [h2], ?_⟩
  simpa only [h3,h4,h5,h6,h7] using pair_invariants a A b

/-- The corresponding five polynomials in the original parameter. -/
def coordinates (a A b c d f t : ℚ) : Fin 5 → ℚ :=
  ![t^3*(a+b*t^5),t^3*(A-b*t^5),t^2*(c+d*t^5),
    t*(1+f*t^5),1-t^5/5]

private lemma sum_expansion (a A b c d f t : ℚ) :
    ∑ i, coordinates a A b c d f t i ^ 5 = (model a A b c d f).eval (t^5) := by
  simp [coordinates,Fin.sum_univ_succ,model]
  ring

/-- Necessity for a pointwise polynomial identity, not only an abstract
polynomial equality. No rational nonexistence theorem is asserted here. -/
theorem constant_identity_necessary (a A b c d f : ℚ)
    (he : ∀ t : ℚ, ∑ i, coordinates a A b c d f t i ^ 5 = 1) :
    f=-c^5/5-2/25 ∧
    firstInvariant (r0 c d f) (r1 c d f) (r2 c d f) (r3 c d f) (r4 c d f)=0 ∧
    secondInvariant (r0 c d f) (r1 c d f) (r2 c d f) (r3 c d f) (r4 c d f)=0 := by
  apply necessary_equations
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun t : ℚ ↦ t^5) := by
    exact (show Odd (5 : ℕ) by decide).pow_injective
  apply (Set.infinite_range_of_injective hinj).mono
  rintro u ⟨t,rfl⟩
  change (model a A b c d f).eval (t^5) = (1 : ℚ[X]).eval (t^5)
  simpa only [sum_expansion,eval_one] using he t

end
end Erdos322Research.QuinticDegreeEight
