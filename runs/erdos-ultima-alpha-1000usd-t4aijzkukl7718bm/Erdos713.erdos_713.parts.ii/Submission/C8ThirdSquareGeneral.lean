import FormalConjecturesUtil
import Submission.C8ThirdPotential

/-! The entire family c²+δab+f(a) has octagons over sufficiently large
finite characteristic-two fields. Auxiliary construction obstruction only. -/
open SimpleGraph Polynomial
namespace Erdos713C8ThirdSquareGeneral
open Erdos713C8FiniteQuadratic Erdos713C8ThirdPotential
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000

lemma exists_poly_value [Fintype K] (p : K[X]) (hp : p ≠ 0)
    (hd : p.natDegree < Fintype.card K) : ∃ x : K, p.eval x ≠ 0 := by
  by_contra! h
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    Function.injective_id h hd)

abbrev detFactor (w : K) := w^8+w^6+w^5+w^3+1

lemma exists_parameter [Fintype K] (hq : 12 < Fintype.card K) :
    ∃ w : K, w ≠ 0 ∧ w+1 ≠ 0 ∧ w^2+w+1 ≠ 0 ∧ detFactor w ≠ 0 := by
  let p : K[X] := X*(X+1)*(X^2+X+1)*(X^8+X^6+X^5+X^3+1)
  have hdeg : p.natDegree = 12 := by dsimp [p]; compute_degree <;> norm_num
  have hp : p ≠ 0 := by intro he; rw [he,Polynomial.natDegree_zero] at hdeg; omega
  obtain ⟨w,hw⟩ := exists_poly_value p hp (hdeg ▸ hq)
  have hh : w*(w+1)*(w^2+w+1)*detFactor w ≠ 0 := by simpa [p,detFactor] using hw
  exact ⟨w,((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).1 |> mul_ne_zero_iff.mp).1,
    ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).1 |> mul_ne_zero_iff.mp).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).1).2,(mul_ne_zero_iff.mp hh).2⟩

abbrev U (w : K) := w^2
abbrev V (w : K) := w^4
abbrev R (w : K) := w*(w+1)
abbrev T (w : K) := w^2*(w^2+1)

lemma base_identity [CharP K 2] (w : K) :
    (R w)^2*V w*(1-V w)-(T w)^2*U w*(1-U w) = 0 := by
  dsimp [U,V,R,T]
  ring_nf
  reduce_mod_char!

lemma D_factor [CharP K 2] (w : K) :
    D (U w) (V w) (R w) (T w) = w^4*(w+1)^4*(w^2+w+1) := by
  dsimp [D,U,V,R,T]
  ring_nf
  reduce_mod_char!
  all_goals ring

lemma det_factor [CharP K 2] (w : K) :
    (D (U w) (V w) (R w) (T w))^3 *
        moment (U w) (V w) (R w) (T w) (fun _ _ c => c^2) +
      (E (U w) (V w) (R w) (T w))^4 =
        w^25*(w+1)^25*detFactor w := by
  dsimp [D,E,U,V,R,T,moment,detFactor]
  ring_nf
  reduce_mod_char!
  all_goals ring

lemma parameters [Fintype K] [CharP K 2] (hq : 12 < Fintype.card K) :
    ∃ u v r t : K, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      r ≠ 0 ∧ t ≠ 0 ∧ r^2*v*(1-v)-t^2*u*(1-u) = 0 ∧ D u v r t ≠ 0 ∧
      (D u v r t)^3*moment u v r t (fun _ _ c => c^2)+(E u v r t)^4 ≠ 0 := by
  obtain ⟨w,hw0,hw1,hw2,hw8⟩ := exists_parameter (K := K) hq
  have hw21 : w^2+1 ≠ 0 := by simpa only [CharTwo.add_sq,one_pow] using pow_ne_zero 2 hw1
  have hu1 : U w ≠ 1 := by
    intro hh
    apply hw21
    change w^2 = 1 at hh
    rw [hh]
    simpa only [one_add_one_eq_two] using (CharTwo.two_eq_zero (R := K))
  have hv1 : V w ≠ 1 := by
    have hh : w^4+1 = (w^2+1)^2 := by rw [CharTwo.add_sq]; ring
    intro he
    have hz : (w^2+1)^2 = 0 := by rw [← hh]; change w^4 = 1 at he; rw [he]; exact (by simpa only [one_add_one_eq_two] using (CharTwo.two_eq_zero (R := K)))
    exact pow_ne_zero 2 hw21 hz
  refine ⟨U w,V w,R w,T w,pow_ne_zero 2 hw0,pow_ne_zero 4 hw0,hu1,hv1,?_,
    mul_ne_zero hw0 hw1,mul_ne_zero (pow_ne_zero 2 hw0) hw21,base_identity w,?_,?_⟩
  · intro he
    have hh : w^2*(w^2+1) = 0 := by
      change w^2 = w^4 at he
      linear_combination -he+w^2*(CharTwo.two_eq_zero (R := K))
    exact mul_ne_zero (pow_ne_zero 2 hw0) hw21 hh
  · rw [D_factor]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hw0) (pow_ne_zero 4 hw1)) hw2
  · rw [det_factor]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 25 hw0) (pow_ne_zero 25 hw1)) hw8

lemma solve_scaled_shift [Fintype K] [CharP K 2] (A B C δ : K)
    (hAB : A+B^4 ≠ 0) (hq : 4 < Fintype.card K) :
    ∃ h τ : K, h ≠ 0 ∧ h^4*A+δ*h*B+C+τ^4+δ*τ = 0 := by
  let p : K[X] := X^4+Polynomial.C δ*X+Polynomial.C C
  have hd : p.natDegree = 4 := by dsimp [p]; compute_degree <;> norm_num
  have hp : p ≠ 0 := by intro he; rw [he,Polynomial.natDegree_zero] at hd; omega
  obtain ⟨z,hz⟩ := exists_poly_value p hp (hd ▸ hq)
  have hz' : z^4+δ*z+C ≠ 0 := by simpa [p] using hz
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  obtain ⟨a,ha⟩ := hSq ((z^4+δ*z+C)/(A+B^4))
  obtain ⟨h,hh⟩ := hSq a
  change h^2 = a at hh
  change a^2 = (z^4+δ*z+C)/(A+B^4) at ha
  have h4 : h^4 = (z^4+δ*z+C)/(A+B^4) := by
    calc
      _ = (h^2)^2 := by ring
      _ = _ := by rw [hh,ha]
  have hh0 : h ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : 4 ≠ 0)] at h4
    exact div_ne_zero hz' hAB h4.symm
  have hmul : h^4*(A+B^4) = z^4+δ*z+C := by rw [h4,div_mul_cancel₀ _ hAB]
  refine ⟨h,B*h+z,hh0,?_⟩
  rw [fourth_add,mul_pow]
  linear_combination hmul+(z^4+δ*z+C+δ*B*h)*(CharTwo.two_eq_zero (R := K))

lemma moment_scale (δ : K) (f : K → K) (u v r t h : K) :
    moment u v (r*h) (t*h) (fun a b c => c^2+δ*a*b+f a) =
      h^5*moment u v r t (fun _ _ c => c^2)+δ*h^2*E u v r t+
        h*moment u v r t (fun a _ _ => f a) := by
  dsimp [moment,E]
  ring

lemma D_scale (u v r t h : K) : D u v (r*h) (t*h) = h*D u v r t := by
  dsimp [D]
  ring

/-- All mixed coefficients are covered, not just noncubes. The slope
summand is an arbitrary function and may depend on the field. -/
theorem contains_square_third [Fintype K] [CharP K 2] (δ : K) (f : K → K)
    (hq : 12 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b c => c^2+δ*a*b+f a) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hD,hdet⟩ := parameters (K := K) hq
  let d := D u v r t
  let e := E u v r t
  let c := moment u v r t (fun _ _ c => c^2)
  let N := moment u v r t (fun a _ _ => f a)
  have hd : d ≠ 0 := hD
  have hAB : c/d+(e/d)^4 ≠ 0 := by
    intro he
    have hh : (c/d+(e/d)^4)*d^4 = d^3*c+e^4 := by field_simp
    rw [he,zero_mul] at hh
    exact hdet hh.symm
  obtain ⟨h,τ,hh0,hzero⟩ := solve_scaled_shift (c/d) (e/d) (N/d) δ hAB (by omega)
  apply Erdos713C8ThirdPotential.contains_of_octagon
  apply Erdos713C8ThirdPotential.shift_octagon τ (Q := fun a b c =>
    (c+2*τ*b+τ^2*a)^2+δ*a*(b+τ*a)+f a)
  · intro a b c; rfl
  · apply octagon_of_moment _ u v (r*h) (t*h) hu hv hu1 hv1 huv
      (mul_ne_zero hr hh0) (mul_ne_zero ht hh0)
    · linear_combination h^2*hB
    · rw [square_third_shift,moment_scale,D_scale]
      change h^5*c+δ*h^2*e+h*N+(τ^4+δ*τ)*(h*d) = 0
      calc
        _ = h*d*(h^4*(c/d)+δ*h*(e/d)+N/d+τ^4+δ*τ) := by field_simp; ring
        _ = 0 := by rw [hzero,mul_zero]

#print axioms det_factor
#print axioms parameters
#print axioms solve_scaled_shift
#print axioms contains_square_third
end Erdos713C8ThirdSquareGeneral
