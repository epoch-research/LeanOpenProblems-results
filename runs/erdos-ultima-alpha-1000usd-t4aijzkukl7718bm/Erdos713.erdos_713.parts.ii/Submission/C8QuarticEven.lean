import FormalConjecturesUtil
import Submission.C8QuarticMixed

/-! Even-mixed quartic translation obstructions for the auxiliary C8 model.
No extremal exponent is asserted here. -/
open SimpleGraph
namespace Erdos713C8QuarticEven
open Erdos713C8FiniteQuadratic Erdos713C8FiniteCubic Erdos713C8QuarticMixed
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

lemma separable_quadratic_zero [Fintype K] [CharP K 2]
    (C d j p q m : K) (hdet : d*p^2+j*q^2 ≠ 0) :
    ∃ s z : K, C*j*s^2+C*d*z^2+p*s+q*z+m = 0 := by
  by_cases hC : C = 0
  · subst C
    by_cases hp : p = 0
    · subst p
      have hq : q ≠ 0 := by intro he; apply hdet; simp [he]
      refine ⟨0,-m/q,?_⟩
      field_simp
      ring
    · refine ⟨-m/p,0,?_⟩
      field_simp
      ring
  · have hSq : Function.Surjective (fun z : K => z^2) :=
      Finite.surjective_of_injective (frobenius_inj K 2)
    obtain ⟨w,hw⟩ := hSq (-m/(C*(d*p^2+j*q^2)))
    change w^2 = -m/(C*(d*p^2+j*q^2)) at hw
    have h0 : C*(d*p^2+j*q^2)*w^2+m = 0 := by
      rw [hw]
      field_simp
      ring
    refine ⟨q*w,-p*w,?_⟩
    linear_combination h0

lemma exists_cubic_value [Fintype K] (F G H I : K)
    (hcoeff : F ≠ 0 ∨ G ≠ 0 ∨ H ≠ 0 ∨ I ≠ 0) (hq : 3 < Fintype.card K) :
    ∃ x : K, F^2+G^2*x+H^2*x^2+I^2*x^3 ≠ 0 := by
  classical
  let p : Polynomial K := Polynomial.C (F^2)+Polynomial.C (G^2)*Polynomial.X+
    Polynomial.C (H^2)*Polynomial.X^2+Polynomial.C (I^2)*Polynomial.X^3
  have hp : p ≠ 0 := by
    intro he
    have h0 := congrArg (fun p : Polynomial K => p.coeff 0) he
    have h1 := congrArg (fun p : Polynomial K => p.coeff 1) he
    have h2 := congrArg (fun p : Polynomial K => p.coeff 2) he
    have h3 := congrArg (fun p : Polynomial K => p.coeff 3) he
    norm_num only [p,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,
      Polynomial.coeff_X,Polynomial.coeff_C,Polynomial.coeff_zero,ite_true,ite_false,
      mul_one,mul_zero,add_zero,zero_add] at h0 h1 h2 h3
    simp only [sq_eq_zero_iff] at h0 h1 h2 h3
    rcases hcoeff with hf | hg | hh | hi <;> contradiction
  have hdeg : p.natDegree ≤ 3 := by
    dsimp [p]
    compute_degree
  by_contra h
  push_neg at h
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Function.injective_id
    (hcard := hdeg.trans_lt hq)
  intro x
  simpa [p] using h x

lemma exists_shear_det [Fintype K] [CharP K 2]
    (d j F G H I : K) (hd : d ≠ 0)
    (hcoeff : F ≠ 0 ∨ G ≠ 0 ∨ H ≠ 0 ∨ I ≠ 0) (hq : 3 < Fintype.card K) :
    ∃ τ : K,
      d*((F+G*τ+H*τ^2+I*τ^3)*d+(H+I*τ)*j)^2+
      j*((G+I*τ^2)*d+I*j)^2 ≠ 0 := by
  obtain ⟨x,hx⟩ := exists_cubic_value F G H I hcoeff hq
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  obtain ⟨τ,hτ⟩ := hSq (x-j/d)
  change τ^2 = x-j/d at hτ
  have hj : j = d*(x-τ^2) := by
    have he : x-τ^2 = j/d := by linear_combination -hτ
    have hh := (eq_div_iff hd).mp he
    linear_combination -hh
  refine ⟨τ,?_⟩
  have he : d*((F+G*τ+H*τ^2+I*τ^3)*d+(H+I*τ)*j)^2+
      j*((G+I*τ^2)*d+I*j)^2 = d^3*(F^2+G^2*x+H^2*x^2+I^2*x^3) := by
    rw [hj]
    simp only [CharTwo.sub_eq_add,CharTwo.add_sq,mul_pow]
    ring_nf
    have h4 : (4 : K) = 0 := by linear_combination 2*(CharTwo.two_eq_zero (R := K))
    simp only [CharTwo.two_eq_zero,h4,mul_zero,add_zero]
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hd) hx

lemma even_translation [CharP K 2]
    (A C E F G H I J L M N O P u v r t s z : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    moment u v r t (fun a b => quartic A 0 C 0 E F G H I J L M N O P (a+s) (b+z)) =
      C*Erdos713C8FiniteQuadratic.J u v r t*s^2+
      C*Erdos713C8FiniteQuadratic.D u v r t*z^2+
      (F*Erdos713C8FiniteQuadratic.D u v r t+H*Erdos713C8FiniteQuadratic.J u v r t)*s+
      (G*Erdos713C8FiniteQuadratic.D u v r t+I*Erdos713C8FiniteQuadratic.J u v r t)*z+
      moment u v r t (quartic A 0 C 0 E F G H I J L M N O P) := by
  rw [moment_quartic_translation A 0 C 0 E F G H I J L M N O P u v r t s z hB]
  simp only [zero_mul,zero_add,add_zero,moment_add,moment_smul,moment_left_sq,moment_right_sq]

lemma even_octagon_of_det [Fintype K] [CharP K 2]
    (A C E F G H I J L M N O P u v r t : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0)
    (hdet : Erdos713C8FiniteQuadratic.D u v r t*
        (F*Erdos713C8FiniteQuadratic.D u v r t+H*Erdos713C8FiniteQuadratic.J u v r t)^2+
      Erdos713C8FiniteQuadratic.J u v r t*
        (G*Erdos713C8FiniteQuadratic.D u v r t+I*Erdos713C8FiniteQuadratic.J u v r t)^2 ≠ 0) :
    Octagon (quartic A 0 C 0 E F G H I J L M N O P) := by
  obtain ⟨s,z,hsz⟩ := separable_quadratic_zero C
    (Erdos713C8FiniteQuadratic.D u v r t) (Erdos713C8FiniteQuadratic.J u v r t)
    (F*Erdos713C8FiniteQuadratic.D u v r t+H*Erdos713C8FiniteQuadratic.J u v r t)
    (G*Erdos713C8FiniteQuadratic.D u v r t+I*Erdos713C8FiniteQuadratic.J u v r t)
    (moment u v r t (quartic A 0 C 0 E F G H I J L M N O P)) hdet
  apply offset_octagon _ s z
  apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
  rw [even_translation A C E F G H I J L M N O P u v r t s z hB]
  exact hsz

theorem even_quartic_with_cubic [Fintype K] [CharP K 2]
    (A C E F G H I J L M N O P : K)
    (hcoeff : F ≠ 0 ∨ G ≠ 0 ∨ H ≠ 0 ∨ I ≠ 0) (hq : 4 < Fintype.card K) :
    Octagon (quartic A 0 C 0 E F G H I J L M N O P) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hd,_⟩ := parameters_char_two (K := K) hq
  obtain ⟨τ,hτ⟩ := exists_shear_det
    (Erdos713C8FiniteQuadratic.D u v r t) (Erdos713C8FiniteQuadratic.J u v r t)
    F G H I hd hcoeff (by omega)
  apply shift_octagon τ (Q := quartic
    (A+C*τ^2+E*τ^4) 0 C 0 E
    (F+G*τ+H*τ^2+I*τ^3) (G+I*τ^2) (H+I*τ) I
    (J+L*τ+M*τ^2) L M (N+O*τ) O P)
  · intro a b
    simpa only [zero_mul,zero_add,add_zero] using
      quartic_shear A 0 C 0 E F G H I J L M N O P a b τ
  · exact even_octagon_of_det _ _ _ _ _ _ _ _ _ _ _ _ _ u v r t
      hu hv hu1 hv1 huv hr ht hB hτ

theorem even_quartic_no_cubic [Fintype K] [CharP K 2]
    (A C E J L M N O P : K) (hC : C ≠ 0) (hq : 4 < Fintype.card K) :
    Octagon (quartic A 0 C 0 E 0 0 0 0 J L M N O P) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hd,_⟩ := parameters_char_two (K := K) hq
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  let m := moment u v r t (quartic A 0 C 0 E 0 0 0 0 J L M N O P)
  obtain ⟨z,hz⟩ := hSq (-m/(C*Erdos713C8FiniteQuadratic.D u v r t))
  change z^2 = -m/(C*Erdos713C8FiniteQuadratic.D u v r t) at hz
  have h0 : C*Erdos713C8FiniteQuadratic.D u v r t*z^2+m=0 := by
    rw [hz]
    field_simp
    ring
  apply offset_octagon _ 0 z
  apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
  rw [even_translation A C E 0 0 0 0 J L M N O P u v r t 0 z hB]
  simpa only [zero_mul,zero_add,add_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] using h0

/-- The even quartic term a²b², or any nonzero cubic term, suffices to
force an octagon. Pure fourth powers and lower terms are unrestricted. -/
theorem even_quartic_nonadditive [Fintype K] [CharP K 2]
    (A C E F G H I J L M N O P : K)
    (hcoeff : C ≠ 0 ∨ F ≠ 0 ∨ G ≠ 0 ∨ H ≠ 0 ∨ I ≠ 0) (hq : 4 < Fintype.card K) :
    Octagon (quartic A 0 C 0 E F G H I J L M N O P) := by
  by_cases h3 : F ≠ 0 ∨ G ≠ 0 ∨ H ≠ 0 ∨ I ≠ 0
  · exact even_quartic_with_cubic A C E F G H I J L M N O P h3 hq
  · have hC := hcoeff.resolve_right h3
    push_neg at h3
    rcases h3 with ⟨rfl,rfl,rfl,rfl⟩
    exact even_quartic_no_cubic A C E J L M N O P hC hq

#print axioms separable_quadratic_zero
#print axioms exists_shear_det
#print axioms even_quartic_nonadditive
end Erdos713C8QuarticEven
