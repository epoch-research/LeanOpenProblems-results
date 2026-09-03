import FormalConjecturesUtil

/-!
Linear-algebraic ingredients for the cubic norm variety. These results do
not yet give a construction settling Erdős 714.
-/
noncomputable section
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

#print axioms four_independent
#print axioms normalized_five_dependence
end Erdos714CubicSegre
