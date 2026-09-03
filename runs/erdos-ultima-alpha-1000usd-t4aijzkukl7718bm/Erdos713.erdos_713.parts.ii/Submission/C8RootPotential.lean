import FormalConjecturesUtil
import Submission.C8FiniteCubic

/-! Inverse-Frobenius potentials in the auxiliary incidence construction.
A nonzero normalized closure is not a freeness proof: a point-coordinate
shift supplies the missing cancellation. This does not settle Erdos 713. -/
open SimpleGraph
namespace Erdos713C8RootPotential
open Erdos713C8FiniteQuadratic Erdos713C8FiniteCubic
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

lemma root_moment_zero [CharP K 2] (σ : K →+* K) (hσ : ∀ a, (σ a)^2=a)
    (u v r t : K) (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a _ => σ a) = 0 := by
  apply sq_eq_zero_iff.mp
  dsimp [moment]
  simp only [map_zero,map_one,zero_mul,one_mul,zero_add,
    CharTwo.sub_eq_add,CharTwo.add_sq,mul_pow,hσ]
  have hB' := hB
  simp only [CharTwo.sub_eq_add] at hB'
  linear_combination hB'

lemma root_product_moment_ne [CharP K 2] (σ : K →+* K) (hσ : ∀ a, (σ a)^2=a)
    (u v r t : K) (hv : v ≠ 0) (hv1 : v ≠ 1) (huv : u ≠ v) (hr : r ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a _ => a*σ a) ≠ 0 := by
  let U := σ u
  let V := σ v
  have hU : U^2 = u := hσ u
  have hV : V^2 = v := hσ v
  have hV0 : V ≠ 0 := by
    intro he
    apply hv
    rw [← hV,he]
    ring
  have hV1 : V ≠ 1 := by
    intro he
    apply hv1
    rw [← hV,he]
    ring
  have hUV : V ≠ U := by
    intro he
    apply huv
    rw [← hU,← hV,he]
  have hz : r*V*(1-V) = t*U*(1-U) := by
    apply (frobenius_inj K 2)
    change (r*V*(1-V))^2 = (t*U*(1-U))^2
    simp only [mul_pow,CharTwo.sub_eq_add,CharTwo.add_sq,one_pow,hU,hV]
    have hB' := hB
    simp only [CharTwo.sub_eq_add] at hB'
    linear_combination hB' - t^2*u*(1+u)*(CharTwo.two_eq_zero (R := K))
  have he : moment u v r t (fun a _ => a*σ a) = r*V*(1-V)*(V-U) := by
    calc
      _ = t*u*(U-1)+r*v*(1-V) := by
        dsimp [moment,U,V]
        simp only [map_zero,map_one,zero_mul,one_mul,zero_add]
        ring
      _ = t*U^2*(U-1)+r*V^2*(1-V) := by rw [hU,hV]
      _ = _ := by linear_combination U*hz
  rw [he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hr hV0) (sub_ne_zero.mpr hV1.symm))
    (sub_ne_zero.mpr hUV)

lemma root_b_shear (σ : K →+* K) (u v r t τ : K) :
    moment u v r t (fun a b => σ a*(b+τ*a)) =
      moment u v r t (fun a b => σ a*b)+τ*moment u v r t (fun a _ => a*σ a) := by
  dsimp [moment]
  ring

/-- This includes potentials whose polynomial degree grows with the field
size, so the fixed-degree quartic result alone does not cover it. -/
theorem root_b_octagon [Fintype K] [CharP K 2]
    (σ : K →+* K) (hσ : ∀ a, (σ a)^2=a) (hq : 4 < Fintype.card K) :
    Octagon (fun a b => σ a*b) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,_⟩ := parameters_char_two (K := K) hq
  let M := moment u v r t (fun a b => σ a*b)
  let N := moment u v r t (fun a _ => a*σ a)
  have hN : N ≠ 0 := root_product_moment_ne σ hσ u v r t hv hv1 huv hr hB
  let τ := -M/N
  apply shift_octagon τ (Q := fun a b => σ a*(b+τ*a))
  · intro a b; rfl
  · apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
    rw [root_b_shear]
    change M+(-M/N)*N=0
    rw [div_mul_cancel₀ _ hN]
    ring

/-- Repeated line slopes give an octagon for every slope-only potential.
No cardinality assumption on the characteristic-two field is required. -/
theorem slope_only_octagon [CharP K 2] (f : K → K) :
    Octagon (fun a _ => f a) := by
  let p : Fin 4 → Vertex K :=
    ![(0,![0,0,0]),(1,![0,0,f 0]),(0,![1,1,f 0+f 1]),(1,![1,0,f 1])]
  let l : Fin 4 → Vertex K :=
    ![(0,![0,0,0]),(1,![1,1,f 0+f 1]),(0,![1,1,f 0+f 1]),(1,![0,0,0])]
  refine ⟨p,l,?_,?_,?_,?_⟩
  · intro i j he
    have hx := congrArg Prod.fst he
    have hy := congrArg (fun v : Vertex K => v.2 0) he
    fin_cases i <;> fin_cases j <;> dsimp [p] at hx hy <;> simp_all
  · intro i j he
    have hx := congrArg Prod.fst he
    have hy := congrArg (fun v : Vertex K => v.2 0) he
    fin_cases i <;> fin_cases j <;> dsimp [l] at hx hy <;> simp_all
  · intro i
    fin_cases i <;> dsimp [Inc,p,l]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring_nf <;> simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  · intro i
    fin_cases i <;> dsimp [Inc,p,l]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring_nf <;> simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]

theorem contains_inverse_frobenius_b [Fintype K] [CharP K 2]
    (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b => (frobeniusEquiv K 2).symm a*b) :=
  contains_of_octagon (root_b_octagon (frobeniusEquiv K 2).symm.toRingHom
    (frobeniusEquiv_symm_pow_p K 2) hq)

theorem contains_slope_only [CharP K 2] (f : K → K) :
    cycleGraph 8 ⊑ graph (fun a _ => f a) := contains_of_octagon (slope_only_octagon f)

#print axioms root_moment_zero
#print axioms root_product_moment_ne
#print axioms contains_inverse_frobenius_b
#print axioms contains_slope_only
end Erdos713C8RootPotential
