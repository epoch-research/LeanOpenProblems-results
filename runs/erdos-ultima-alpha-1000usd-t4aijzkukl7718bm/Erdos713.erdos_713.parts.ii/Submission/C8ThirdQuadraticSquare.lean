import FormalConjecturesUtil
import Submission.C8ThirdSquareGeneral
import Submission.FiniteAdditiveTwoVariable

/-! Adding a quadratic intercept term does not repair this characteristic-two
incidence construction. This is not a solution of Erdős 713. -/
open SimpleGraph Polynomial
namespace Erdos713C8ThirdQuadraticSquare
open Erdos713C8FiniteQuadratic Erdos713C8ThirdPotential Erdos713C8ThirdSquareGeneral
open Erdos713FiniteAdditiveTwoVariable (determinant quartic_pair_solve_nonzero)
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000

abbrev compatibility (B δ w : K) :=
  δ^4*(detFactor w)^3+B^6*w^6*(w+1)^6*(w^2+w+1)^4

lemma exists_parameter [Fintype K] (B δ : K) (hB : B ≠ 0)
    (hq : 28 < Fintype.card K) :
    ∃ w : K, w ≠ 0 ∧ w+1 ≠ 0 ∧ w^2+w+1 ≠ 0 ∧ compatibility B δ w ≠ 0 := by
  let p : K[X] := Polynomial.C (δ^4)*(X^8+X^6+X^5+X^3+1)^3+
    Polynomial.C (B^6)*X^6*(X+1)^6*(X^2+X+1)^4
  have hp : p ≠ 0 := by
    by_cases hδ : δ = 0
    · have hd : p.natDegree = 20 := by
        dsimp [p]
        simp only [hδ,zero_pow (by decide : 4 ≠ 0),Polynomial.C_0,zero_mul,zero_add]
        compute_degree <;> norm_num [hB]
      intro he
      rw [he,Polynomial.natDegree_zero] at hd
      omega
    · have hd : p.natDegree = 24 := by
        dsimp [p]
        compute_degree <;> norm_num [hδ,hB]
      intro he
      rw [he,Polynomial.natDegree_zero] at hd
      omega
  let q : K[X] := X*(X+1)*(X^2+X+1)*p
  have hq0 : q ≠ 0 := by
    apply mul_ne_zero _ hp
    apply mul_ne_zero
    · apply mul_ne_zero X_ne_zero
      exact X_add_C_ne_zero 1
    · intro he
      have hd : (X^2+X+1 : K[X]).natDegree = 2 := by compute_degree; norm_num
      rw [he,Polynomial.natDegree_zero] at hd
      omega
  have hd : q.natDegree ≤ 28 := by dsimp [q,p]; compute_degree
  obtain ⟨w,hw⟩ := Erdos713C8ThirdSquareGeneral.exists_poly_value q hq0 (hd.trans_lt hq)
  have hh : w*(w+1)*(w^2+w+1)*compatibility B δ w ≠ 0 := by
    simpa [q,p,compatibility,detFactor] using hw
  exact ⟨w,((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).1 |> mul_ne_zero_iff.mp).1,
    ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).1 |> mul_ne_zero_iff.mp).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).2,(mul_ne_zero_iff.mp hh).2⟩

lemma Cn_factor [CharP K 2] (w : K) :
    D (U w) (V w) (R w) (T w)*J (U w) (V w) (R w) (T w)+
      (E (U w) (V w) (R w) (T w))^2 = w^14*(w+1)^14 := by
  dsimp [D,J,E,U,V,R,T]
  ring_nf
  reduce_mod_char!
  all_goals ring

lemma Sn_factor [CharP K 2] (w : K) :
    D (U w) (V w) (R w) (T w)*
        moment (U w) (V w) (R w) (T w) (fun _ _ c => c^2)+
      (J (U w) (V w) (R w) (T w))^2 = w^17*(w+1)^17*(w^2+w+1)^2 := by
  dsimp [D,J,moment,U,V,R,T]
  ring_nf
  reduce_mod_char!
  all_goals ring

lemma cleared_determinant [CharP K 2] (B δ d e c j : K) (hd : d ≠ 0) :
    determinant (c/d+(e/d)^4) B (j/d+(e/d)^2) δ*d^12 =
      δ^4*(d^3*c+e^4)^3+B^6*(d*j+e^2)^4*(d*c+j^2)*d^2 := by
  dsimp [determinant]
  field_simp
  ring_nf
  reduce_mod_char!

lemma parameter_determinant [CharP K 2] (B δ w : K)
    (hd : D (U w) (V w) (R w) (T w) ≠ 0) (hw : w ≠ 0) (hw1 : w+1 ≠ 0)
    (hc : compatibility B δ w ≠ 0) :
    determinant
      (moment (U w) (V w) (R w) (T w) (fun _ _ c => c^2)/D (U w) (V w) (R w) (T w)+
        (E (U w) (V w) (R w) (T w)/D (U w) (V w) (R w) (T w))^4)
      B (J (U w) (V w) (R w) (T w)/D (U w) (V w) (R w) (T w)+
        (E (U w) (V w) (R w) (T w)/D (U w) (V w) (R w) (T w))^2) δ ≠ 0 := by
  intro he
  have hh := cleared_determinant B δ (D (U w) (V w) (R w) (T w))
    (E (U w) (V w) (R w) (T w))
    (moment (U w) (V w) (R w) (T w) (fun _ _ c => c^2))
    (J (U w) (V w) (R w) (T w)) hd
  rw [he,zero_mul,det_factor,Cn_factor,Sn_factor,D_factor] at hh
  have hid : δ^4*(w^25*(w+1)^25*detFactor w)^3+
      B^6*(w^14*(w+1)^14)^4*(w^17*(w+1)^17*(w^2+w+1)^2)*
        (w^4*(w+1)^4*(w^2+w+1))^2 =
      w^75*(w+1)^75*compatibility B δ w := by dsimp [compatibility]; ring
  rw [hid] at hh
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hw1)) hc hh.symm

lemma moment_shift [CharP K 2] (B δ : K) (f : K → K) (u v r t τ : K) :
    moment u v r t (fun a b c =>
      (c+2*τ*b+τ^2*a)^2+B*(b+τ*a)^2+δ*a*(b+τ*a)+f a) =
    moment u v r t (fun a b c => c^2+B*b^2+δ*a*b+f a)+
      (τ^4+B*τ^2+δ*τ)*D u v r t := by
  simp only [CharTwo.two_eq_zero,zero_mul,add_zero,CharTwo.add_sq,mul_pow]
  dsimp [moment,D]
  ring

lemma moment_scale (B δ : K) (f : K → K) (u v r t h : K) :
    moment u v (r*h) (t*h) (fun a b c => c^2+B*b^2+δ*a*b+f a) =
      h^5*moment u v r t (fun _ _ c => c^2)+B*h^3*J u v r t+
        δ*h^2*E u v r t+h*moment u v r t (fun a _ _ => f a) := by
  dsimp [moment,J,E]
  ring

lemma solve_scaled_shift [Fintype K] [CharP K 2] (a b c B δ N : K)
    (hdet : determinant (a+b^4) B (c+b^2) δ ≠ 0)
    (hq : 4 < Fintype.card K) :
    ∃ h τ : K, h ≠ 0 ∧ h^4*a+B*h^2*c+δ*h*b+N+τ^4+B*τ^2+δ*τ = 0 := by
  obtain ⟨h,z,hh,hz⟩ := quartic_pair_solve_nonzero (a+b^4) B (c+b^2) δ N hdet hq
  refine ⟨h,b*h+z,hh,?_⟩
  rw [Erdos713C8ThirdPotential.fourth_add,CharTwo.add_sq,mul_pow,mul_pow]
  linear_combination hz+(N+δ*b*h)*(CharTwo.two_eq_zero (R := K))

/-- The extra intercept-square coefficient is arbitrary, as are the mixed
coefficient and the entire slope function. The conclusion is an injective C8
copy in the full incidence graph, not an assertion about restricted graphs. -/
theorem contains_quadratic_square [Fintype K] [CharP K 2] (B δ : K) (f : K → K)
    (hq : 28 < Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8ThirdPotential.graph (fun a b c => c^2+B*b^2+δ*a*b+f a) := by
  by_cases hB : B = 0
  · simpa [hB] using contains_square_third δ f (by omega : 12 < Fintype.card K)
  obtain ⟨w,hw0,hw1,hw2,hwc⟩ := exists_parameter B δ hB hq
  have hw21 : w^2+1 ≠ 0 := by
    simpa only [CharTwo.add_sq,one_pow] using pow_ne_zero 2 hw1
  have hu1 : U w ≠ 1 := by
    intro hh
    apply hw21
    change w^2 = 1 at hh
    rw [hh]
    simpa only [one_add_one_eq_two] using (CharTwo.two_eq_zero (R := K))
  have hv1 : V w ≠ 1 := by
    have hh : w^4+1 = (w^2+1)^2 := by rw [CharTwo.add_sq]; ring
    intro he
    have hz : (w^2+1)^2 = 0 := by
      rw [← hh]
      change w^4 = 1 at he
      rw [he]
      simpa only [one_add_one_eq_two] using (CharTwo.two_eq_zero (R := K))
    exact pow_ne_zero 2 hw21 hz
  have huv : U w ≠ V w := by
    intro he
    have hh : w^2*(w^2+1) = 0 := by
      change w^2 = w^4 at he
      linear_combination -he+w^2*(CharTwo.two_eq_zero (R := K))
    exact mul_ne_zero (pow_ne_zero 2 hw0) hw21 hh
  have hr : R w ≠ 0 := mul_ne_zero hw0 hw1
  have ht : T w ≠ 0 := mul_ne_zero (pow_ne_zero 2 hw0) hw21
  have hd : D (U w) (V w) (R w) (T w) ≠ 0 := by
    rw [D_factor]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hw0) (pow_ne_zero 4 hw1)) hw2
  let d := D (U w) (V w) (R w) (T w)
  let e := E (U w) (V w) (R w) (T w)
  let j := J (U w) (V w) (R w) (T w)
  let c := moment (U w) (V w) (R w) (T w) (fun _ _ c => c^2)
  let N := moment (U w) (V w) (R w) (T w) (fun a _ _ => f a)
  have hd' : d ≠ 0 := hd
  have hdet : determinant (c/d+(e/d)^4) B (j/d+(e/d)^2) δ ≠ 0 :=
    parameter_determinant B δ w hd hw0 hw1 hwc
  obtain ⟨h,τ,hh0,hzero⟩ := solve_scaled_shift (c/d) (e/d) (j/d) B δ (N/d) hdet (by omega)
  apply Erdos713C8ThirdPotential.contains_of_octagon
  apply Erdos713C8ThirdPotential.shift_octagon τ (Q := fun a b c =>
    (c+2*τ*b+τ^2*a)^2+B*(b+τ*a)^2+δ*a*(b+τ*a)+f a)
  · intro a b c; rfl
  · apply octagon_of_moment _ (U w) (V w) (R w*h) (T w*h)
      (pow_ne_zero 2 hw0) (pow_ne_zero 4 hw0) hu1 hv1 huv
      (mul_ne_zero hr hh0) (mul_ne_zero ht hh0)
    · linear_combination h^2*base_identity w
    · rw [moment_shift,moment_scale,D_scale]
      change h^5*c+B*h^3*j+δ*h^2*e+h*N+(τ^4+B*τ^2+δ*τ)*(h*d) = 0
      calc
        _ = h*d*(h^4*(c/d)+B*h^2*(j/d)+δ*h*(e/d)+N/d+τ^4+B*τ^2+δ*τ) := by
          field_simp
          ring
        _ = 0 := by rw [hzero,mul_zero]

#print axioms exists_parameter
#print axioms parameter_determinant
#print axioms solve_scaled_shift
#print axioms contains_quadratic_square
end Erdos713C8ThirdQuadraticSquare
