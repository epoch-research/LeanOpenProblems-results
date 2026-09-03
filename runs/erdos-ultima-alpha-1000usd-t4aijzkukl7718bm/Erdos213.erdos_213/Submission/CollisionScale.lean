import Submission.CollisionEquilateral

/-! The remaining quartic for two equilateral collision anchors.
The universal-square hypothesis is essential: these results do not classify
square values at individual parameter choices. -/
namespace Erdos213.CollisionEquilateral
open Polynomial Erdos213.CircleLineRigidity
noncomputable section

/-- The radial polynomial of an anchor with nonzero initial scale l. -/
def anchorFactor (l : ℝ) : ℝ[X] := C l-C (1/2)*X-C (3/(16*l))*X^2

def anchorMutual (l : ℝ) : ℝ[X] :=
  (anchorFactor 1)^2+anchorFactor 1*anchorFactor l+(anchorFactor l)^2

lemma anchor_expansion (l : ℝ) (hl : l ≠ 0) :
    anchorMutual l = C (l^2+l+1)+C (-3*(l+1)/2)*X+
      C (-3*(l^2+1)/(16*l))*X^2+C (9*(l+1)/(32*l))*X^3+
      C (9*(l^2+l+1)/(256*l^2))*X^4 := by
  apply Polynomial.funext
  intro t
  simp [anchorMutual,anchorFactor]
  field_simp
  ring

/-- Coefficients zero through three already force the two possible scales. -/
lemma scale_coefficient_obstruction (l p0 p1 p2 : ℝ)
    (h0 : p0^2=l^2+l+1)
    (h1 : 4*p0*p1 = -3*(l+1))
    (h2 : 16*l*(p1^2+2*p0*p2) = -3*(l^2+1))
    (h3 : 64*l*p1*p2 = 9*(l+1)) : l=1 ∨ l = -1 := by
  by_cases hp : p1=0
  · right
    simp only [hp,mul_zero] at h1
    linarith
  have he : p1*(16*l*p2+3*p0)=0 := by linear_combination (h3+3*h1)/4
  have he' := (mul_eq_zero.mp he).resolve_left hp
  have hg : 16*l*p1^2=3*(l+1)^2 := by
    linear_combination h2-2*p0*he'+6*h0
  have hsq : 16*p0^2*p1^2=9*(l+1)^2 := by
    have hh := congrArg (fun x : ℝ => x^2) h1
    nlinarith only [hh]
  have hf : (l-1)^2*(l+1)^2=0 := by
    linear_combination -(p0^2/3)*hg+(l/3)*hsq-(l+1)^2*h0
  rcases mul_eq_zero.mp hf with h | h
  · left
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  · right
    have he := sq_eq_zero_iff.mp h
    linarith

lemma anchor_square_scales (l : ℝ) (hl : l ≠ 0) (hs : IsSquare (anchorMutual l)) :
    l=1 ∨ l = -1 := by
  obtain ⟨p,hp⟩ := hs
  have hp0 : p ≠ 0 := by
    intro hz
    have he := congrArg (fun q : ℝ[X] => q.coeff 0) hp
    rw [anchor_expansion l hl,hz] at he
    simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,mul_zero,coeff_zero] at he
    norm_num at he
    nlinarith [sq_nonneg (l+1/2)]
  have hd : (anchorMutual l).natDegree ≤ 4 := by
    rw [anchor_expansion l hl]
    compute_degree!
  have hdeg := congrArg (fun q : ℝ[X] => q.natDegree) hp
  change (anchorMutual l).natDegree=(p*p).natDegree at hdeg
  rw [natDegree_mul hp0 hp0] at hdeg
  have hpdeg : p.natDegree < 3 := by omega
  have hrep := p.as_sum_range_C_mul_X_pow' hpdeg
  have hpsq : p*p = C ((p.coeff 0)^2)+C (2*p.coeff 0*p.coeff 1)*X+
      C ((p.coeff 1)^2+2*p.coeff 0*p.coeff 2)*X^2+
      C (2*p.coeff 1*p.coeff 2)*X^3+C ((p.coeff 2)^2)*X^4 := by
    apply Polynomial.funext
    intro t
    conv_lhs => rw [hrep]
    simp [Finset.sum_range_succ]
    ring
  rw [anchor_expansion l hl,hpsq] at hp
  have h0 := congrArg (fun q : ℝ[X] => q.coeff 0) hp
  have h1 := congrArg (fun q : ℝ[X] => q.coeff 1) hp
  have h2 := congrArg (fun q : ℝ[X] => q.coeff 2) hp
  have h3 := congrArg (fun q : ℝ[X] => q.coeff 3) hp
  simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  apply scale_coefficient_obstruction l (p.coeff 0) (p.coeff 1) (p.coeff 2)
  · exact h0.symm
  · linarith
  · field_simp at h2
    nlinarith [h2]
  · field_simp at h3
    nlinarith [h3]

lemma anchor_one_square : IsSquare (anchorMutual 1) := by
  refine ⟨C (Real.sqrt 3)*anchorFactor 1,?_⟩
  have he : (C (Real.sqrt 3) : ℝ[X])*C (Real.sqrt 3)=C 3 := by
    rw [← C_mul]
    congr 1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    anchorMutual 1 = C 3*(anchorFactor 1*anchorFactor 1) := by
      dsimp [anchorMutual]
      simp only [map_ofNat]
      ring
    _ = _ := by rw [← he]; ring

lemma anchor_neg_one_square : IsSquare (anchorMutual (-1)) := by
  refine ⟨C 1+C (3/16)*X^2,?_⟩
  apply Polynomial.funext
  intro t
  norm_num [anchorMutual,anchorFactor]
  ring

/-- Complete real rational-function classification for this normalized quartic. -/
lemma anchor_ratFunc_square_iff (l : ℝ) (hl : l ≠ 0) :
    IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (anchorMutual l)) ↔ l=1 ∨ l = -1 := by
  constructor
  · intro h
    exact anchor_square_scales l hl (polynomial_square_of_ratFunc_square _ h)
  · rintro (rfl | rfl)
    · obtain ⟨p,hp⟩ := anchor_one_square
      exact ⟨algebraMap ℝ[X] (RatFunc ℝ) p, by simp [← map_mul,← hp]⟩
    · obtain ⟨p,hp⟩ := anchor_neg_one_square
      exact ⟨algebraMap ℝ[X] (RatFunc ℝ) p, by simp [← map_mul,← hp]⟩

def charPoint (x y : ℝ) : ℂ := (x : ℂ)+(y*Real.sqrt 3)*Complex.I

lemma charPoint_dist_sq (x y X Y : ℝ) :
    dist (charPoint x y) (charPoint X Y)^2=(x-X)^2+3*(y-Y)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp [charPoint,Complex.mul_re,Complex.mul_im]
  linear_combination (y-Y)^2*(Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

/-- Equal anchor scales always give a concyclic quadruple (possibly with
coincident vertices at exceptional times). -/
lemma equal_scale_cospherical (t s : ℝ) :
    EuclideanGeometry.Cospherical
      ({charPoint t 0,charPoint (-t/2) (t/2),charPoint s 0,
        charPoint (-s/2) (s/2)} : Set ℂ) := by
  let K : ℝ := t^2+t*s+s^2
  have hK : 0 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg (t+s),sq_nonneg (t-s)]
  let o := charPoint ((t+s)/2) ((t+s)/2)
  refine ⟨o,Real.sqrt K,?_⟩
  rintro p (rfl | rfl | rfl | rfl)
  all_goals
    apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg K)).mp
    rw [Real.sq_sqrt hK]
    dsimp [o]
    rw [charPoint_dist_sq]
    dsimp [K]
    ring

lemma anchor_one_eval (t : ℝ) : (anchorFactor 1).eval t=f t := by
  norm_num [anchorFactor,f]
  ring
lemma anchor_neg_one_eval (t : ℝ) : (anchorFactor (-1)).eval t=g t := by
  norm_num [anchorFactor,g]
  ring

lemma isolated_interpolation (t : ℝ) :
    (anchorMutual 2).eval t-(-(27*t^2+28*t-160)/64)^2 =
      -(t+4)*(3*t-8)*(3*t-4)*(53*t-24)/4096 := by
  norm_num [anchorMutual,anchorFactor]
  ring

lemma isolated_square_value :
    (anchorMutual 2).eval (24/53) = ((6223/2809 : ℝ))^2 := by
  norm_num [anchorMutual,anchorFactor]

lemma isolated_not_universal :
    ¬ IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (anchorMutual 2)) := by
  rw [anchor_ratFunc_square_iff 2 (by norm_num)]
  norm_num

#print axioms isolated_interpolation
#print axioms isolated_square_value
#print axioms isolated_not_universal
#print axioms equal_scale_cospherical
#print axioms scale_coefficient_obstruction
#print axioms anchor_square_scales
#print axioms anchor_ratFunc_square_iff
end
end Erdos213.CollisionEquilateral
