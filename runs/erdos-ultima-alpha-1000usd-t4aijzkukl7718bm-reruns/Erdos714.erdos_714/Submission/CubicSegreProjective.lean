import Submission.CubicSegre

/-!
Five-point dependence in the cubic norm variety: after a projective change
of parameter, all five points lie on a line over the fixed field. This is
an ingredient for a larger-biclique bound, not a solution of Erdős 714.
-/
noncomputable section
open Classical Finset
set_option maxHeartbeats 4000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The product of three conjugates, valued in the extension field. -/
def norm (σ : E →+* E) (x : E) : E := x*σ x*σ (σ x)

lemma norm_ne_zero (σ : E →+* E) {x : E} (hx : x ≠ 0) : norm σ x ≠ 0 :=
  mul_ne_zero (mul_ne_zero hx ((map_ne_zero σ).mpr hx))
    ((map_ne_zero σ).mpr ((map_ne_zero σ).mpr hx))

lemma norm_mul (σ : E →+* E) (x y : E) : norm σ (x*y) = norm σ x*norm σ y := by
  simp only [norm,map_mul]
  ring

lemma norm_div (σ : E →+* E) (x y : E) : norm σ (x/y) = norm σ x/norm σ y := by
  simp only [norm,map_div₀]
  ring

/-- Homogeneous coordinates, including the point at infinity. -/
def homogeneous (σ : E →+* E) (u v : E) : Fin 8 → E :=
  ![norm σ v, u*σ v*σ (σ v), v*σ u*σ (σ v), v*σ v*σ (σ u),
    u*σ u*σ (σ v), u*σ v*σ (σ u), v*σ u*σ (σ u), norm σ u]

lemma homogeneous_div (σ : E →+* E) (u v : E) (hv : v ≠ 0) :
    homogeneous σ u v = norm σ v • point σ (u/v) := by
  have hv₁ : σ v ≠ 0 := (map_ne_zero σ).mpr hv
  have hv₂ : σ (σ v) ≠ 0 := (map_ne_zero σ).mpr hv₁
  ext i
  fin_cases i <;> simp [homogeneous,point,segre,norm,map_div₀] <;> field_simp

/-- Tensoring the three conjugate two-dimensional changes of coordinates. -/
def transform (σ : E →+* E) (a b c d : E) : (Fin 8 → E) →ₗ[E] (Fin 8 → E) where
  toFun v := ![
    functional c d (σ c) (σ d) (σ (σ c)) (σ (σ d)) v,
    functional a b (σ c) (σ d) (σ (σ c)) (σ (σ d)) v,
    functional c d (σ a) (σ b) (σ (σ c)) (σ (σ d)) v,
    functional c d (σ c) (σ d) (σ (σ a)) (σ (σ b)) v,
    functional a b (σ a) (σ b) (σ (σ c)) (σ (σ d)) v,
    functional a b (σ c) (σ d) (σ (σ a)) (σ (σ b)) v,
    functional c d (σ a) (σ b) (σ (σ a)) (σ (σ b)) v,
    functional a b (σ a) (σ b) (σ (σ a)) (σ (σ b)) v]
  map_add' := by intro v w; ext i; fin_cases i <;> simp
  map_smul' := by intro k v; ext i; fin_cases i <;> simp

lemma transform_point (σ : E →+* E) (a b c d x : E) :
    transform σ a b c d (point σ x) = homogeneous σ (a*x+b) (c*x+d) := by
  ext i
  fin_cases i <;> simp [transform,point,functional_segre,homogeneous,norm,map_add,map_mul]

/-- Every coefficient in a nonzero relation on five distinct points is nonzero. -/
theorem five_relation_nonzero (σ : E →+* E) (x : Fin 5 → E) (hx : Function.Injective x)
    (coeff : Fin 5 → E) (h : ∑ i, coeff i • point σ (x i) = 0)
    (hn : ∃ i, coeff i ≠ 0) : ∀ i, coeff i ≠ 0 := by
  intro j hj
  have he := h
  rw [Fin.sum_univ_succAbove _ j,hj,zero_smul,zero_add] at he
  have hh := four_relation σ (fun i => x (j.succAbove i))
    (hx.comp Fin.succAbove_right_injective) (fun i => coeff (j.succAbove i)) he
  obtain ⟨i,hi⟩ := hn
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k,rfl⟩
  · exact hi hj
  · exact hi (hh k)

/-- The cross-ratio parameter sending the first three points to infinity, zero, one. -/
def parameter (x : Fin 5 → E) (i : Fin 5) : E :=
  ((x 2-x 0)/(x 2-x 1))*(x i-x 1)/(x i-x 0)

/-- The nontrivial remaining parameters in a five-point dependence are fixed. -/
theorem dependent_parameters_fixed (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x : Fin 5 → E) (hx : Function.Injective x)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) :
    σ (parameter x 3) = parameter x 3 ∧ σ (parameter x 4) = parameter x 4 := by
  obtain ⟨coeff,hrel,hn⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hc := five_relation_nonzero σ x hx coeff hrel hn
  let k := (x 2-x 0)/(x 2-x 1)
  let U (i : Fin 5) := k*x i-k*x 1
  let V (i : Fin 5) := x i-x 0
  have hv (i : Fin 5) (hi : i ≠ 0) : V i ≠ 0 := sub_ne_zero.mpr (hx.ne hi)
  have hu₁ : U 1 = 0 := by dsimp [U]; ring
  have hu₂ : U 2 = V 2 := by
    dsimp [U,V,k]
    have hh : x 2-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
    field_simp
  have hv₀ : V 0 = 0 := by simp [V]
  have hp (i : Fin 5) : U i/V i = parameter x i := by dsimp [U,V,k,parameter]; ring
  have htr : ∑ i, coeff i • homogeneous σ (U i) (V i) = 0 := by
    have he := congrArg (transform σ k (-k*x 1) 1 (-x 0)) hrel
    simpa only [map_sum,map_smul,map_zero,transform_point,one_mul,neg_mul,
      ← sub_eq_add_neg,U,V] using he
  have hform (i : Fin 5) (hi : i ≠ 0) :
      homogeneous σ (U i) (V i) = norm σ (V i) • point σ (parameter x i) := by
    rw [homogeneous_div σ _ _ (hv i hi),hp]
  have hp₁ : parameter x 1 = 0 := by simp [parameter]
  have hp₂ : parameter x 2 = 1 := by
    rw [← hp 2,hu₂,div_self (hv 2 (by decide))]
  have hcoord (j : Fin 8) (hj₀ : j ≠ 0) (hj₇ : j ≠ 7) :
      (coeff 2*norm σ (V 2))+
      (coeff 3*norm σ (V 3))*point σ (parameter x 3) j+
      (coeff 4*norm σ (V 4))*point σ (parameter x 4) j = 0 := by
    have he := congrArg (fun v : Fin 8 → E => v j) htr
    simp only [Fin.sum_univ_five,Pi.add_apply,Pi.zero_apply,Pi.smul_apply,smul_eq_mul] at he
    rw [hform 1 (by decide),hform 2 (by decide),hform 3 (by decide),hform 4 (by decide),
      hp₁,hp₂] at he
    fin_cases j <;> simp_all [homogeneous,point,segre,norm,mul_assoc]
  apply normalized_five_dependence σ hσ
    (coeff 2*norm σ (V 2)) (coeff 3*norm σ (V 3)) (coeff 4*norm σ (V 4))
    (parameter x 3) (parameter x 4)
    (mul_ne_zero (hc 2) (norm_ne_zero σ (hv 2 (by decide))))
    (mul_ne_zero (hc 3) (norm_ne_zero σ (hv 3 (by decide))))
    (mul_ne_zero (hc 4) (norm_ne_zero σ (hv 4 (by decide))))
  all_goals first
    | simpa [point,segre,mul_assoc] using hcoord 1 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 2 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 3 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 4 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 5 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 6 (by decide) (by decide)

#print axioms homogeneous_div
#print axioms five_relation_nonzero
#print axioms dependent_parameters_fixed
end Erdos714CubicSegre
