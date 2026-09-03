import FormalConjecturesUtil

/-! Self-contained cubic norm graph K55 construction. Not a solution of Erdős714. -/

noncomputable section

/-
Linear-algebraic ingredients for the cubic norm variety. These results do
not yet give a construction settling Erdős 714.
-/
open Classical Finset
set_option maxHeartbeats 2000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- Affine coordinates on the product of three projective lines. -/
def segre (x y z : E) : Fin 8 → E := ![1,x,y,z,x*y,x*z,y*z,x*y*z]

def point (σ : E →+* E) (x : E) : Fin 8 → E := segre x (σ x) (σ (σ x))

/-- Every product of three affine factors is a linear functional in Segre coordinates. -/
def functional (a b c d e f : E) : (Fin 8 → E) →ₗ[E] E where
  toFun v := b*d*f*v 0+a*d*f*v 1+b*c*f*v 2+b*d*e*v 3+
    a*c*f*v 4+a*d*e*v 5+b*c*e*v 6+a*c*e*v 7
  map_add' := by intro v w; simp only [Pi.add_apply]; ring
  map_smul' := by intro k v; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma functional_segre (a b c d e f x y z : E) :
    functional a b c d e f (segre x y z) = (a*x+b)*(c*y+d)*(e*z+f) := by
  simp [functional,segre]
  ring

lemma functional_relation {I : Type*} [Fintype I] (σ : E →+* E)
    (x coeff : I → E) (h : ∑ i, coeff i • point σ (x i) = 0)
    (a b c d e f : E) :
    ∑ i, coeff i*((a*x i+b)*(c*σ (x i)+d)*(e*σ (σ (x i))+f)) = 0 := by
  have he := congrArg (functional a b c d e f) h
  simpa only [map_sum,map_smul,map_zero,point,functional_segre,smul_eq_mul] using he

/-- A product of three coordinate factors isolates one of four distinct points. -/
theorem four_relation (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x)
    (coeff : Fin 4 → E) (h : ∑ i, coeff i • point σ (x i) = 0) : ∀ i, coeff i = 0 := by
  have hn (i j : Fin 4) (hij : i ≠ j) : x i-x j ≠ 0 := sub_ne_zero.mpr (hx.ne hij)
  have hn₁ (i j : Fin 4) (hij : i ≠ j) : σ (x i)-σ (x j) ≠ 0 :=
    sub_ne_zero.mpr (σ.injective.ne (hx.ne hij))
  have hn₂ (i j : Fin 4) (hij : i ≠ j) : σ (σ (x i))-σ (σ (x j)) ≠ 0 :=
    sub_ne_zero.mpr (σ.injective.ne (σ.injective.ne (hx.ne hij)))
  intro i
  fin_cases i
  · have he := functional_relation σ x coeff h 1 (-x 1) 1 (-σ (x 2)) 1 (-σ (σ (x 3)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 0 1 (by decide)) (hn₁ 0 2 (by decide))) (hn₂ 0 3 (by decide)))
  · have he := functional_relation σ x coeff h 1 (-x 0) 1 (-σ (x 2)) 1 (-σ (σ (x 3)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 1 0 (by decide)) (hn₁ 1 2 (by decide))) (hn₂ 1 3 (by decide)))
  · have he := functional_relation σ x coeff h 1 (-x 0) 1 (-σ (x 1)) 1 (-σ (σ (x 3)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 2 0 (by decide)) (hn₁ 2 1 (by decide))) (hn₂ 2 3 (by decide)))
  · have he := functional_relation σ x coeff h 1 (-x 0) 1 (-σ (x 1)) 1 (-σ (σ (x 2)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 3 0 (by decide)) (hn₁ 3 1 (by decide))) (hn₂ 3 2 (by decide)))

/-- The cubic norm variety has four-point linear independence over the extension field. -/
theorem four_independent (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x) :
    LinearIndependent E (fun i => point σ (x i)) := by
  rw [Fintype.linearIndependent_iff]
  exact four_relation σ x hx

/-- Eliminate the second coordinate from singleton and pair moment relations. -/
lemma pair_eliminate (a b c z w u v : E)
    (h₁ : a+b*z+c*w = 0) (h₂ : a+b*u+c*v = 0)
    (h₁₂ : a+b*z*u+c*w*v = 0) :
    b*(b+c)*z*u+a*b*(z+u)+a*(a+c) = 0 := by
  linear_combination c*h₁₂+(a+b*u)*h₁-c*w*h₂

/-- Three conjugates are either all equal or pairwise distinct. -/
lemma orbit_distinct (σ : E →+* E) (hσ : ∀ x, σ (σ (σ x)) = x)
    (z : E) (hz : σ z ≠ z) :
    z ≠ σ z ∧ σ z ≠ σ (σ z) ∧ z ≠ σ (σ z) := by
  refine ⟨Ne.symm hz,?_,?_⟩
  · intro he
    exact hz (σ.injective he).symm
  · intro he
    have hh := congrArg σ he
    rw [hσ] at hh
    exact hz hh

/-- After normalizing three projective points to infinity, zero, and one,
a nontrivial five-point dependence forces the other two parameters to be fixed.
No assumption that the dependence coefficients lie in the fixed field is needed. -/
theorem normalized_five_dependence (σ : E →+* E) (hσ : ∀ x, σ (σ (σ x)) = x)
    (a b c z w : E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₀ : a+b*z+c*w = 0)
    (h₁ : a+b*σ z+c*σ w = 0)
    (h₂ : a+b*σ (σ z)+c*σ (σ w) = 0)
    (h₀₁ : a+b*z*σ z+c*w*σ w = 0)
    (h₀₂ : a+b*z*σ (σ z)+c*w*σ (σ w) = 0)
    (h₁₂ : a+b*σ z*σ (σ z)+c*σ w*σ (σ w) = 0) :
    σ z = z ∧ σ w = w := by
  have hz : σ z = z := by
    by_contra hn
    obtain ⟨hne₀₁,hne₁₂,hne₀₂⟩ := orbit_distinct σ hσ z hn
    have e₀₁ := pair_eliminate a b c z w (σ z) (σ w) h₀ h₁ h₀₁
    have e₀₂ := pair_eliminate a b c z w (σ (σ z)) (σ (σ w)) h₀ h₂ h₀₂
    have e₁₂ := pair_eliminate a b c (σ z) (σ w) (σ (σ z)) (σ (σ w)) h₁ h₂ h₁₂
    have hp : b*(b+c)*z+a*b = 0 := by
      apply (mul_eq_zero.mp (show (σ z-σ (σ z))*(b*(b+c)*z+a*b) = 0 by
        linear_combination e₀₁-e₀₂)).resolve_left (sub_ne_zero.mpr hne₁₂)
    have hq : b*(b+c)*σ z+a*b = 0 := by
      apply (mul_eq_zero.mp (show (z-σ (σ z))*(b*(b+c)*σ z+a*b) = 0 by
        linear_combination e₀₁-e₁₂)).resolve_left (sub_ne_zero.mpr hne₀₂)
    have hA : b*(b+c) = 0 := by
      apply (mul_eq_zero.mp (show b*(b+c)*(z-σ z) = 0 by
        linear_combination hp-hq)).resolve_right (sub_ne_zero.mpr hne₀₁)
    rw [hA,zero_mul,zero_add] at hp
    exact mul_ne_zero ha hb hp
  refine ⟨hz,?_⟩
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show c*(σ w-w) = 0 by
    rw [hz] at h₁
    linear_combination h₁-h₀)).resolve_left hc

end Erdos714CubicSegre


/-
Five-point dependence in the cubic norm variety: after a projective change
of parameter, all five points lie on a line over the fixed field. This is
an ingredient for a larger-biclique bound, not a solution of Erdős 714.
-/
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

end Erdos714CubicSegre


/-
Common-neighbor bounds for dependent rows of a cubic norm graph.
This is not a resolution of Erdős 714.
-/
open Classical Finset Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The cubic norm polynomial on shifts fixed by the automorphism. -/
def shift (σ : E →+* E) (z : E) : E[X] :=
  (X+C z)*(X+C (σ z))*(X+C (σ (σ z)))

lemma shift_degree (σ : E →+* E) (z : E) : (shift σ z).natDegree ≤ 3 := by
  unfold shift
  compute_degree!

lemma shift_monic (σ : E →+* E) (z : E) : (shift σ z).Monic :=
  ((monic_X_add_C _).mul (monic_X_add_C _)).mul (monic_X_add_C _)

lemma shift_eval (σ : E →+* E) (z t : E) (ht : σ t = t) :
    (shift σ z).eval t = norm σ (z+t) := by
  simp only [shift,eval_mul,eval_add,eval_X,eval_C,norm,map_add,ht]
  ring

lemma shift_root (σ : E →+* E) (z : E) : (shift σ z).eval (-z) = 0 := by
  simp [shift]

/-- Four distinct fixed scalar shifts recover the complete cubic polynomial. -/
lemma shift_recovery (σ : E →+* E) (z w : E) (t : Fin 4 → E)
    (ht : Function.Injective t) (hfix : ∀ i, σ (t i) = t i)
    (h : ∀ i, norm σ (z+t i) = norm σ (w+t i)) : shift σ z = shift σ w := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
  · intro i
    simp only [eval_sub,shift_eval σ _ _ (hfix i),h i,sub_self]
  · have hd := (natDegree_sub_le (shift σ z) (shift σ w)).trans
      (max_le (shift_degree σ z) (shift_degree σ w))
    simpa using (show (shift σ z-shift σ w).natDegree < 4 by omega)

/-- Four norm spheres centered on a fixed-field affine line have at most
three common points. The five-point contradiction is enough for K55. -/
theorem no_five_sphere_points (σ : E →+* E) (A B : E) (hA : A ≠ 0)
    (t : Fin 4 → E) (ht : Function.Injective t) (hfix : ∀ i, σ (t i) = t i)
    (y : Fin 5 → E) (hy : Function.Injective y) (c : Fin 4 → E)
    (h : ∀ i j, norm σ (A*t i+B+y j) = c i) : False := by
  let z (j : Fin 5) := (B+y j)/A
  have hz : Function.Injective z := by
    intro i j hij
    apply hy
    apply add_left_cancel (a := B)
    exact (div_left_inj' hA).mp hij
  have he (i : Fin 4) (j : Fin 5) : A*(z j+t i) = A*t i+B+y j := by
    dsimp [z]
    field_simp
    ring
  have hsame (j : Fin 5) : shift σ (z j) = shift σ (z 0) := by
    apply shift_recovery σ _ _ t ht hfix
    intro i
    apply mul_left_cancel₀ (norm_ne_zero σ hA)
    rw [← norm_mul,← norm_mul,he,he,h i j,h i 0]
  have hzero : shift σ (z 0) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (neg_injective.comp hz)
    · intro j
      rw [← hsame j]
      exact shift_root σ (z j)
    · have hd := shift_degree σ (z 0)
      simpa using (show (shift σ (z 0)).natDegree < 5 by omega)
  exact (shift_monic σ (z 0)).ne_zero hzero

/-- Reciprocal coordinates turn the dependent five-point set into four
centers on a fixed-field affine line. -/
theorem dependent_reciprocal_line (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x : Fin 5 → E) (hx : Function.Injective x)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) :
    ∃ A B : E, A ≠ 0 ∧ ∃ t : Fin 4 → E, Function.Injective t ∧
      (∀ i, σ (t i) = t i) ∧ ∀ i, (x i.succ-x 0)⁻¹ = A*t i+B := by
  let k := (x 2-x 0)/(x 2-x 1)
  let A := (k*(x 0-x 1))⁻¹
  let B := -(x 0-x 1)⁻¹
  let t (i : Fin 4) := parameter x i.succ
  have h₂₀ : x 2-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have h₂₁ : x 2-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have h₀₁ : x 0-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have hk : k ≠ 0 := div_ne_zero h₂₀ h₂₁
  have ha : A ≠ 0 := inv_ne_zero (mul_ne_zero hk h₀₁)
  have hform (i : Fin 4) : (x i.succ-x 0)⁻¹ = A*t i+B := by
    have hi : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
    dsimp [A,B,t,parameter,k]
    field_simp
    ring
  refine ⟨A,B,ha,t,?_,?_,hform⟩
  · intro i j hij
    have hv : (x i.succ-x 0)⁻¹ = (x j.succ-x 0)⁻¹ := by rw [hform,hform,hij]
    exact Fin.succ_injective 4 (hx (sub_left_injective (inv_injective hv)))
  · obtain ⟨h₃,h₄⟩ := dependent_parameters_fixed σ hσ x hx hdep
    have hp₁ : parameter x 1 = 0 := by simp [parameter]
    have hp₂ : parameter x 2 = 1 := by
      dsimp [parameter]
      field_simp
    intro i
    fin_cases i
    · simp [t,hp₁]
    · simp [t,hp₂]
    · exact h₃
    · exact h₄

/-- Dependent five rows cannot have five distinct common column points.
Both nonzero weights needed in the reciprocal normalization are explicit. -/
theorem dependent_no_rectangle (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x y : Fin 5 → E) (hx : Function.Injective x) (hy : Function.Injective y)
    (a b : Fin 5 → E) (ha : a 0 ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) : False := by
  obtain ⟨A,B,hA,t,ht,hfix,hform⟩ := dependent_reciprocal_line σ hσ x hx hdep
  have hsum (j : Fin 5) : x 0+y j ≠ 0 := by
    intro he
    have hn := h 0 j
    rw [he] at hn
    have hz : norm σ (0 : E) = 0 := by simp [norm]
    rw [hz] at hn
    exact mul_ne_zero ha (hb j) hn.symm
  let w (j : Fin 5) := (x 0+y j)⁻¹
  have hw : Function.Injective w := by
    intro i j hij
    exact hy (add_left_cancel (inv_injective hij))
  let c (i : Fin 4) := a i.succ/(a 0*norm σ (x i.succ-x 0))
  apply no_five_sphere_points σ A B hA t ht hfix w hw c
  intro i j
  rw [← hform]
  have hd : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
  have he : (x i.succ-x 0)⁻¹+w j =
      (x i.succ+y j)/((x i.succ-x 0)*(x 0+y j)) := by
    dsimp [w]
    field_simp [hsum j]
    ring
  rw [he,norm_div,norm_mul,h i.succ j,h 0 j]
  dsimp [c]
  field_simp [hb j,norm_ne_zero σ hd]

end Erdos714CubicSegre

open SimpleGraph
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The norm of a sum is the pairing of complementary Segre coordinates. -/
lemma complement_pairing (σ : E →+* E) (x y : E) :
    ∑ i : Fin 8, point σ x i*point σ y i.rev = norm σ (x+y) := by
  simp [Fin.sum_univ_succ,point,segre,norm,map_add]
  ring

/-- Independent rows on both sides cannot be orthogonal in dimension nine. -/
theorem independent_no_rectangle (σ : E →+* E)
    (x y a b : Fin 5 → E)
    (hx : LinearIndependent E (fun i => point σ (x i)))
    (hy : LinearIndependent E (fun j => point σ (y j)))
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : False := by
  let A : Matrix (Fin 5) (Fin 9) E := fun i => Fin.snoc (point σ (x i)) (a i)
  let B : Matrix (Fin 9) (Fin 5) E := fun k j =>
    (Fin.snoc (fun l : Fin 8 => point σ (y j) l.rev) (-b j) : Fin 9 → E) k
  have hA : LinearIndependent E A.row := by
    apply LinearIndependent.of_comp (LinearMap.funLeft E E (fun i : Fin 8 => i.castSucc))
    simpa [A,Function.comp_def,Matrix.row,LinearMap.funLeft] using hx
  have hB : LinearIndependent E B.transpose.row := by
    apply LinearIndependent.of_comp
      (LinearMap.funLeft E E (fun i : Fin 8 => i.rev.castSucc))
    simpa [B,Function.comp_def,Matrix.row,Matrix.transpose_apply,LinearMap.funLeft] using hy
  have hAB : A*B = 0 := by
    ext i j
    change ∑ k : Fin 9, A i k*B k j = 0
    rw [Fin.sum_univ_castSucc]
    simp only [A,B,Fin.snoc_castSucc,Fin.snoc_last]
    rw [complement_pairing,h i j]
    ring
  have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hAB
  rw [hA.rank_matrix,← Matrix.rank_transpose B,hB.rank_matrix] at hr
  norm_num at hr

/-- All row configurations, including the linearly dependent ones, are handled. -/
theorem no_five_rectangle (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x y : Fin 5 → E) (hx : Function.Injective x) (hy : Function.Injective y)
    (a b : Fin 5 → E) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : False := by
  by_cases hi : LinearIndependent E (fun i => point σ (x i))
  · by_cases hj : LinearIndependent E (fun j => point σ (y j))
    · exact independent_no_rectangle σ x y a b hi hj h
    · exact dependent_no_rectangle σ hσ y x hy hx b a (hb 0) ha
        (fun j i => by simpa [add_comm,mul_comm] using h i j) hj
  · exact dependent_no_rectangle σ hσ x y hx hy a b (ha 0) hb h hi


end Erdos714CubicSegre

namespace Erdos714CubicSegre
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- Two copies of the ordinary weighted cubic norm graph. -/
def normGraph : SimpleGraph (Bool × (E × Fˣ)) where
  Adj p q := p.1 ≠ q.1 ∧ Algebra.norm F (p.2.1+q.2.1) = (p.2.2 : F)*(q.2.2 : F)
  symm := by intro p q h; exact ⟨h.1.symm,by simpa [add_comm,mul_comm] using h.2⟩
  loopless := by intro p h; exact h.1 rfl

private lemma same_side {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

omit [Fintype F] [Fintype E] in
/-- The conjugate formula is sufficient for freeness of the actual field-norm graph. -/
theorem graph_free_of_norm_formula (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (hN : ∀ z, algebraMap F E (Algebra.norm F z) = norm σ z) :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Free (normGraph (F := F) (E := E)) := by
  rintro ⟨f⟩
  let L (i : Fin 5) := f (Sum.inl i)
  let R (j : Fin 5) := f (Sum.inr j)
  have he (i j : Fin 5) : (normGraph (F := F) (E := E)).Adj (L i) (R j) :=
    f.toHom.map_adj (by simp)
  have hx : Function.Injective (fun i => (L i).2.1) := by
    intro i j hij
    change (L i).2.1 = (L j).2.1 at hij
    have hw : ((L i).2.2 : F) = ((L j).2.2 : F) := by
      apply mul_right_cancel₀ (R 0).2.2.ne_zero
      rw [← (he i 0).2,← (he j 0).2,hij]
    have hv : L i = L j := Prod.ext (same_side (he i 0).1 (he j 0).1)
      (Prod.ext hij (Units.ext hw))
    exact Sum.inl.inj (f.injective hv)
  have hy : Function.Injective (fun j => (R j).2.1) := by
    intro i j hij
    change (R i).2.1 = (R j).2.1 at hij
    have hw : ((R i).2.2 : F) = ((R j).2.2 : F) := by
      apply mul_left_cancel₀ (L 0).2.2.ne_zero
      rw [← (he 0 i).2,← (he 0 j).2,hij]
    have hv : R i = R j := Prod.ext (same_side (he 0 i).1.symm (he 0 j).1.symm)
      (Prod.ext hij (Units.ext hw))
    exact Sum.inr.inj (f.injective hv)
  apply no_five_rectangle σ hσ (fun i => (L i).2.1) (fun j => (R j).2.1) hx hy
    (fun i => algebraMap F E ((L i).2.2 : F)) (fun j => algebraMap F E ((R j).2.2 : F))
    (fun i => (_root_.map_ne_zero _).mpr (L i).2.2.ne_zero)
    (fun j => (_root_.map_ne_zero _).mpr (R j).2.2.ne_zero)
  intro i j
  rw [← hN,(he i j).2,map_mul]

/-- Uniform K55-freeness in every finite cubic extension, all characteristics. -/
theorem normGraph_free (hdim : Module.finrank F E = 3) :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Free (normGraph (F := F) (E := E)) := by
  let σ : E →+* E := (FiniteField.frobeniusAlgHom F E).toRingHom
  have hcard : Fintype.card E = Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E),hdim]
  have hσ : ∀ z, σ (σ (σ z)) = z := by
    intro z
    change ((z^Fintype.card F)^Fintype.card F)^Fintype.card F = z
    rw [← pow_mul,← pow_mul,show Fintype.card F*(Fintype.card F*Fintype.card F) =
      Fintype.card F^3 by ring,← hcard]
    exact FiniteField.pow_card z
  apply graph_free_of_norm_formula σ hσ
  intro z
  change algebraMap F E (Algebra.norm F z) =
    z*(z^Fintype.card F)*((z^Fintype.card F)^Fintype.card F)
  rw [FiniteField.algebraMap_norm_eq_prod_pow F E z,hdim]
  simp only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,one_mul,
    Nat.card_eq_fintype_card,← pow_mul,pow_two]

/-- A neighbor is uniquely determined by its nonzero sum coordinate. -/
def normNeighborEquiv (p : Bool × (E × Fˣ)) :
    (normGraph (F := F) (E := E)).neighborSet p ≃ Eˣ where
  toFun q := Units.mk0 (p.2.1+q.val.2.1) (by
    have hn : Algebra.norm F (p.2.1+q.val.2.1) ≠ 0 := by
      rw [q.property.2]
      exact mul_ne_zero p.2.2.ne_zero q.val.2.2.ne_zero
    exact Algebra.norm_ne_zero_iff.mp hn)
  invFun z := ⟨(!p.1,((z : E)-p.2.1,Units.map (Algebra.norm F (S := E)) z/p.2.2)),by
    constructor
    · cases p.1 <;> simp
    · simp only [Units.val_div_eq_div_val]
      change Algebra.norm F (p.2.1+((z : E)-p.2.1)) =
        (p.2.2 : F)*(Algebra.norm F (z : E)/(p.2.2 : F))
      rw [show p.2.1+((z : E)-p.2.1) = (z : E) by ring]
      field_simp⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · change (!p.1) = q.val.1
      have hs := q.property.1
      cases hp : p.1 <;> cases hq : q.val.1 <;> simp_all
    · apply Prod.ext
      · change p.2.1+q.val.2.1-p.2.1 = q.val.2.1
        ring
      · apply Units.ext
        simp only [Units.val_div_eq_div_val]
        change Algebra.norm F (p.2.1+q.val.2.1)/(p.2.2 : F) = (q.val.2.2 : F)
        rw [q.property.2]
        field_simp
  right_inv z := by
    apply Units.ext
    change p.2.1+((z : E)-p.2.1) = (z : E)
    ring

lemma normGraph_degree (p : Bool × (E × Fˣ)) :
    (normGraph (F := F) (E := E)).degree p = Fintype.card E-1 := by
  rw [← card_neighborSet_eq_degree,← Fintype.card_units]
  exact Fintype.card_congr (normNeighborEquiv p)

/-- Exact number of unordered edges. -/
theorem normGraph_edges (hdim : Module.finrank F E = 3) :
    (normGraph (F := F) (E := E)).edgeFinset.card =
      Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) := by
  have h := (normGraph (F := F) (E := E)).sum_degrees_eq_twice_card_edges
  simp only [normGraph_degree,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_bool,Fintype.card_units,nsmul_eq_mul,Nat.cast_id,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim] at h
  nlinarith

end Erdos714CubicSegre
#print axioms Erdos714CubicSegre.normGraph_free
#print axioms Erdos714CubicSegre.normGraph_edges
end
