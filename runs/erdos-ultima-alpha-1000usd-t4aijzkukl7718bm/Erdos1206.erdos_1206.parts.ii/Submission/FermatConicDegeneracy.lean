import Submission.FermatCubicConics

/-!
Rank-degenerate quadratic families have identically zero linearized cubic.
Auxiliary geometric rigidity; no density result is asserted.
-/

namespace Erdos1206.FermatConicDegeneracy
open Polynomial FermatCubicConics FermatCubicSubspaces

def cone (x : Vec) : ℚ := x 0*x 2-(x 1)^2

private noncomputable def polarDirection (v : Vec) : Vec →ₗ[ℚ] ℚ :=
  linear ![v 2,-2*v 1,v 0]

private lemma cone_not_product {M L : Vec →ₗ[ℚ] ℚ} {k : ℚ}
    (he : ∀ x, M x*L x+k*cone x=0) : k=0 := by
  let u : Vec := ![1,0,0]
  let v : Vec := ![0,1,0]
  let w : Vec := ![0,0,1]
  have h₀ : M u*L u=0 := by simpa [u,cone] using he u
  have h₁ : M v*L v=k := by have hh := he v; norm_num [v,cone] at hh; linarith
  have h₂ : M w*L w=0 := by simpa [w,cone] using he w
  have h₀₁ : (M u+M v)*(L u+L v)-k=0 := by
    have hh := he (u+v)
    simp only [map_add] at hh
    simpa [u,v,cone,sub_eq_add_neg] using hh
  have h₀₂ : (M u+M w)*(L u+L w)+k=0 := by
    have hh := he (u+w)
    simp only [map_add] at hh
    simpa [u,w,cone] using hh
  by_contra hk
  have hMv : M v ≠ 0 := by intro hz; simp [hz] at h₁; exact hk h₁.symm
  have hLv : L v ≠ 0 := by intro hz; simp [hz] at h₁; exact hk h₁.symm
  have hc : M u*L v+M v*L u=0 := by nlinarith only [h₀,h₁,h₀₁]
  have hu : M u=0 ∧ L u=0 := by
    rcases mul_eq_zero.mp h₀ with hm | hl
    · refine ⟨hm,?_⟩
      rw [hm,zero_mul,zero_add] at hc
      exact (mul_eq_zero.mp hc).resolve_left hMv
    · refine ⟨?_,hl⟩
      rw [hl,mul_zero,add_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_right hLv
  rw [hu.1,hu.2,zero_add,zero_add,h₂,zero_add] at h₀₂
  exact hk h₀₂

private lemma product_linear_zero {M L : Vec →ₗ[ℚ] ℚ}
    (he : ∀ x, M x*L x=0) : M=0 ∨ L=0 := by
  by_cases hM : M=0
  · exact Or.inl hM
  right
  obtain ⟨u,hu⟩ := DFunLike.ne_iff.mp hM
  change M u ≠ 0 at hu
  have hLu : L u=0 := (mul_eq_zero.mp (he u)).resolve_left hu
  apply LinearMap.ext
  intro x
  change L x=0
  by_cases hx : M x=0
  · have hMu : M (x+u) ≠ 0 := by simpa [map_add,hx] using hu
    have hz := (mul_eq_zero.mp (he (x+u))).resolve_left hMu
    simpa [map_add,hLu] using hz
  · exact (mul_eq_zero.mp (he x)).resolve_left hx

private lemma polar_zero {v : Vec} (he : polarDirection v=0) : v=0 := by
  have h₀ := congrArg (fun f : Vec →ₗ[ℚ] ℚ => f ![1,0,0]) he
  have h₁ := congrArg (fun f : Vec →ₗ[ℚ] ℚ => f ![0,1,0]) he
  have h₂ := congrArg (fun f : Vec →ₗ[ℚ] ℚ => f ![0,0,1]) he
  norm_num [polarDirection,linear] at h₀ h₁ h₂
  ext i
  fin_cases i <;> simp_all

/-- A product of the Veronese cone with a nonzero linear form cannot be
invariant under a nonzero translation direction. -/
theorem cone_linear_translation_rigid {L : Vec →ₗ[ℚ] ℚ} {v : Vec} (hv : v ≠ 0)
    (he : ∀ (x : Vec) (t : ℚ), cone (x+t • v)*L (x+t • v)=cone x*L x) : L=0 := by
  have hdir (x : Vec) : polarDirection v x*L x+cone x*L v=0 := by
    have h₁ := he x 1
    have hm := he x (-1)
    have h₂ := he x 2
    simp only [map_add,map_smul,smul_eq_mul,cone,Pi.add_apply,Pi.smul_apply] at h₁ hm h₂
    dsimp [polarDirection,linear,cone]
    linear_combination (-1/6:ℚ)*h₂+h₁-(1/3:ℚ)*hm
  have hLv : L v=0 := cone_not_product (M := polarDirection v) (L := L) (fun x => by simpa only [mul_comm (cone x)] using hdir x)
  have hp : ∀ x, polarDirection v x*L x=0 := by
    intro x
    simpa [hLv] using hdir x
  rcases product_linear_zero hp with hM | hL
  · exact (hv (polar_zero hM)).elim
  · exact hL

/-- The noninjective case has zero residual form. -/
theorem residual_zero_of_not_jointlyInjective {a b c d : Vec}
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0)
    (hj : ¬ JointlyInjective (linear a) (linear b) (linear c) (linear d)) :
    residual a b c d=0 := by
  classical
  simp only [JointlyInjective,not_forall] at hj
  obtain ⟨v,hv⟩ := hj
  push_neg at hv
  obtain ⟨ha,hb,hc,hd,hv⟩ := hv
  apply cone_linear_translation_rigid hv
  intro x t
  dsimp only [cone]
  rw [← conic_factorization he (x+t • v),← conic_factorization he x]
  simp only [map_add,map_smul,smul_eq_mul,ha,hb,hc,hd,mul_zero,add_zero]


/-- Joint injectivity is exactly nonvanishing of the residual line. -/
theorem jointlyInjective_iff_residual_ne_zero {a b c d : Vec}
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0) :
    JointlyInjective (linear a) (linear b) (linear c) (linear d) ↔ residual a b c d ≠ 0 := by
  constructor
  · exact fun hj => residual_ne_zero hj he
  · intro hr
    by_contra hj
    exact hr (residual_zero_of_not_jointlyInjective he hj)

/-- A degenerate quadratic image satisfies the cubic identity on its entire
linearized image, not merely on its parametrized conic. -/
theorem cubic_zero_of_not_jointlyInjective {a b c d : Vec}
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0)
    (hj : ¬ JointlyInjective (linear a) (linear b) (linear c) (linear d)) :
    ∀ x, (linear a x)^3+(linear b x)^3+(linear c x)^3+(linear d x)^3=0 := by
  intro x
  rw [conic_factorization he x,residual_zero_of_not_jointlyInjective he hj]
  simp

private noncomputable def linearPolynomial (L : Vec →ₗ[ℚ] ℚ) : ℚ[X] :=
  quad ![L ![1,0,0],L ![0,1,0],L ![0,0,1]]

private lemma linear_coordinates (L : Vec →ₗ[ℚ] ℚ) (x : Vec) :
    L x=L ![1,0,0]*x 0+L ![0,1,0]*x 1+L ![0,0,1]*x 2 := by
  have hx : x=x 0 • ![1,0,0]+x 1 • ![0,1,0]+x 2 • ![0,0,1] := by
    ext i
    fin_cases i <;> simp
  calc
    L x=L (x 0 • ![1,0,0]+x 1 • ![0,1,0]+x 2 • ![0,0,1]) := congrArg L hx
    _ = _ := by simp only [map_add,map_smul,smul_eq_mul]; ring

private lemma linearPolynomial_eval (L : Vec →ₗ[ℚ] ℚ) (t : ℚ) :
    (linearPolynomial L).eval t=L ![t^2,t,1] := by
  rw [linear_coordinates L ![t^2,t,1]]
  simp [linearPolynomial,quad]

private lemma quad_scalar_of_linear {a : Vec} {L : Vec →ₗ[ℚ] ℚ} {r : ℚ}
    (he : linear a=r • L) : quad a=C r*linearPolynomial L := by
  apply Polynomial.funext
  intro t
  have hh := congrArg (fun f : Vec →ₗ[ℚ] ℚ => f ![t^2,t,1]) he
  simp only [eval_mul,eval_C,linearPolynomial_eval]
  simpa [quad,linear,LinearMap.smul_apply,smul_eq_mul] using hh

private lemma quad_pair_zero {a b : Vec} (he : linear a+linear b=0) : quad a+quad b=0 := by
  apply Polynomial.funext
  intro t
  have hh := congrArg (fun f : Vec →ₗ[ℚ] ℚ => f ![t^2,t,1]) he
  simpa [quad,linear] using hh

/-- All rank-degenerate quadratic families are either the three trivial
pairings or common polynomial dilations of a constant four-tuple. -/
theorem degenerate_family_classification {a b c d : Vec}
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0)
    (hj : ¬ JointlyInjective (linear a) (linear b) (linear c) (linear d)) :
    FermatCubicLines.OppositePairs (quad a) (quad b) (quad c) (quad d) ∨
      FermatCubicLines.CommonFactor (quad a) (quad b) (quad c) (quad d) := by
  rcases linear_forms_opposite_or_common (cubic_zero_of_not_jointlyInjective he hj) with hp | hp
  · left
    rcases hp with ⟨hab,hcd⟩ | ⟨hac,hbd⟩ | ⟨had,hbc⟩
    · exact Or.inl ⟨quad_pair_zero hab,quad_pair_zero hcd⟩
    · exact Or.inr (Or.inl ⟨quad_pair_zero hac,quad_pair_zero hbd⟩)
    · exact Or.inr (Or.inr ⟨quad_pair_zero had,quad_pair_zero hbc⟩)
  · right
    obtain ⟨L,r,s,t,w,ha,hb,hc,hd⟩ := hp
    exact ⟨linearPolynomial L,r,s,t,w,quad_scalar_of_linear ha,
      quad_scalar_of_linear hb,quad_scalar_of_linear hc,quad_scalar_of_linear hd⟩

private lemma pair_dependent_zero_left {p q : ℚ[X]} (hp : p=0) :
    PolynomialPairDependent p q := by
  exact ⟨1,0,Or.inl one_ne_zero,by simp [hp]⟩

private lemma pair_dependent_common {a b c d : ℚ[X]}
    (hp : FermatCubicLines.CommonFactor a b c d) : PolynomialPairDependent (a+b) (c+d) := by
  obtain ⟨q,r,s,t,w,ha,hb,hc,hd⟩ := hp
  by_cases hrs : r+s=0
  · apply pair_dependent_zero_left
    rw [ha,hb]
    calc
      C r*q+C s*q=C (r+s)*q := by simp only [map_add]; ring
      _ = 0 := by simp [hrs]
  · refine ⟨t+w,-(r+s),Or.inr (neg_ne_zero.mpr hrs),?_⟩
    rw [ha,hb,hc,hd]
    simp only [map_add,map_neg]
    ring

/-- The three rational pair-relation alternatives now cover ALL quadratic
families, including every rank degeneracy. This is not yet the classification
of three simultaneous representations or a statement about density. -/
theorem quadratic_pair_relation_all {a b c d : Vec}
    (he : quad a^3+quad b^3+quad c^3+quad d^3=0) :
    PolynomialPairDependent (quad a+quad b) (quad c+quad d) ∨
    PolynomialPairDependent (quad a+quad c) (quad b+quad d) ∨
    PolynomialPairDependent (quad a+quad d) (quad b+quad c) := by
  classical
  by_cases hj : JointlyInjective (linear a) (linear b) (linear c) (linear d)
  · exact quadratic_pair_relation hj he
  rcases degenerate_family_classification he hj with hp | hp
  · rcases hp with ⟨hab,_⟩ | ⟨hac,_⟩ | ⟨had,_⟩
    · exact Or.inl (pair_dependent_zero_left hab)
    · exact Or.inr (Or.inl (pair_dependent_zero_left hac))
    · exact Or.inr (Or.inr (pair_dependent_zero_left had))
  · exact Or.inl (pair_dependent_common hp)

#print axioms degenerate_family_classification
#print axioms quadratic_pair_relation_all

#print axioms cone_linear_translation_rigid
#print axioms jointlyInjective_iff_residual_ne_zero
#print axioms cubic_zero_of_not_jointlyInjective
end Erdos1206.FermatConicDegeneracy
