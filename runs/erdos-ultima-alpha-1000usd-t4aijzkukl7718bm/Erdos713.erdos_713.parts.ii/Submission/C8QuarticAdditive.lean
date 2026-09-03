import FormalConjecturesUtil
import Submission.C8QuarticEven

/-! Additive fourth-power terms in the auxiliary C8 incidence model. -/
open SimpleGraph
namespace Erdos713C8QuarticAdditive
open Erdos713C8FiniteQuadratic Erdos713C8FiniteCubic
open Erdos713C8QuarticMixed Erdos713C8QuarticEven
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

lemma exists_poly_value [Fintype K] (p : Polynomial K) (hp : p ≠ 0)
    (hdeg : p.natDegree < Fintype.card K) : ∃ x : K, p.eval x ≠ 0 := by
  by_contra h
  push_neg at h
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Function.injective_id h hdeg)

def U (u v r t : K) : K := (u^4-u)*t+(v-v^4)*r

def V (u v r t : K) : K :=
  (u*((1-v)*r-(1-u)*t))^4*t+((1-v)*r)^4*(v*r-u*t)

lemma moment_left_four (u v r t : K) :
    moment u v r t (fun a _ => a^4) = U u v r t := by
  dsimp [moment,U]
  ring

lemma moment_right_four (u v r t : K) :
    moment u v r t (fun _ b => b^4) = V u v r t := by
  dsimp [moment,V]
  ring

lemma complement_four [CharP K 2] (u : K) :
    (1-u)^4-(1-u) = u^4-u := by
  simp only [CharTwo.sub_eq_add,add_four_char_two,one_pow]
  linear_combination CharTwo.two_eq_zero (R := K)

/-- A base octagon with both its second- and fourth-power slope moments
nonzero. The field-size assumption excludes the roots of a degree-eight
polynomial; it is not a heuristic genericity assumption. -/
lemma fourth_parameters [Fintype K] [CharP K 2] (hq : 8 < Fintype.card K) :
    ∃ u v r t : K,
      u ≠ 0 ∧ v ≠ 0 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ r ≠ 0 ∧ t ≠ 0 ∧
      r^2*v*(1-v)-t^2*u*(1-u) = 0 ∧
      D u v r t ≠ 0 ∧ U u v r t ≠ 0 := by
  classical
  obtain ⟨u,_,_,_,hu,_,hu1,_⟩ := parameters_char_two (K := K) (by omega)
  let p : Polynomial K :=
    Polynomial.X*(1-Polynomial.X)*Polynomial.C ((u^4-u)^2) -
    Polynomial.C (u*(1-u))*(Polynomial.X^4-Polynomial.X)^2
  have hcoeff : p.coeff 8 = -(u*(1-u)) := by
    have he : p = Polynomial.C (-(u*(1-u)))*Polynomial.X^8+
        Polynomial.C (2*u*(1-u))*Polynomial.X^5+
        Polynomial.C (-(u^4-u)^2-u*(1-u))*Polynomial.X^2+
        Polynomial.C ((u^4-u)^2)*Polynomial.X := by
      dsimp [p]
      simp only [Polynomial.C_neg,Polynomial.C_sub,Polynomial.C_mul,
        Polynomial.C_pow,Polynomial.C_ofNat,Polynomial.C_1]
      ring
    rw [he]
    norm_num only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C_mul_X,
      ite_true,ite_false,add_zero]
  have hp : p ≠ 0 := by
    intro he
    have h := congrArg (fun p : Polynomial K => p.coeff 8) he
    change p.coeff 8 = (0 : Polynomial K).coeff 8 at h
    rw [hcoeff,Polynomial.coeff_zero] at h
    exact (neg_ne_zero.mpr (mul_ne_zero hu (sub_ne_zero.mpr hu1.symm))) h
  have hdeg : p.natDegree ≤ 8 := by dsimp [p]; compute_degree
  obtain ⟨v,hv⟩ := exists_poly_value p hp (hdeg.trans_lt hq)
  have hev (x : K) : p.eval x = x*(1-x)*(u^4-u)^2-u*(1-u)*(x^4-x)^2 := by
    simp [p]
  have hv0 : v ≠ 0 := by intro he; subst v; apply hv; simp [p]
  have hv1 : v ≠ 1 := by intro he; subst v; apply hv; simp [p]
  have hvu : v ≠ u := by intro he; subst v; apply hv; rw [hev]; ring
  have hvc : v ≠ 1-u := by
    intro he; subst v; apply hv
    rw [hev,complement_four]
    ring
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  obtain ⟨r,hr⟩ := hSq (u*(1-u))
  obtain ⟨t,ht⟩ := hSq (v*(1-v))
  change r^2 = u*(1-u) at hr
  change t^2 = v*(1-v) at ht
  have hr0 : r ≠ 0 := by
    intro he; rw [he,zero_pow (by decide : 2 ≠ 0)] at hr
    exact (mul_ne_zero hu (sub_ne_zero.mpr hu1.symm)) hr.symm
  have ht0 : t ≠ 0 := by
    intro he; rw [he,zero_pow (by decide : 2 ≠ 0)] at ht
    exact (mul_ne_zero hv0 (sub_ne_zero.mpr hv1.symm)) ht.symm
  have hrt : r ≠ t := by
    intro he
    have hh : (v-u)*(v-(1-u)) = 0 := by
      rw [he] at hr
      linear_combination ht-hr
    exact (mul_ne_zero (sub_ne_zero.mpr hvu) (sub_ne_zero.mpr hvc)) hh
  have hB : r^2*v*(1-v)-t^2*u*(1-u) = 0 := by rw [hr,ht]; ring
  have hD : D u v r t ≠ 0 := by
    have he : D u v r t = r*t*(t-r) := by
      dsimp [D]
      linear_combination t*hr-r*ht
    rw [he]
    exact mul_ne_zero (mul_ne_zero hr0 ht0) (sub_ne_zero.mpr hrt.symm)
  refine ⟨u,v,r,t,hu,hv0,hu1,hv1,hvu.symm,hr0,ht0,hB,hD,?_⟩
  intro he
  apply hv
  have heq : (U u v r t)^2 = p.eval v := by
    rw [hev]
    dsimp [U]
    simp only [CharTwo.sub_eq_add,CharTwo.add_sq,mul_pow,hr,ht]
    ring
  rw [← heq,he]
  ring

/-- A one-sided simultaneous scaling of slope and intercept. -/
def pointScale (σ : K) (p : Vertex K) : Vertex K :=
  (p.1,![σ*p.2 0,σ*p.2 1,p.2 2])

def lineScale (σ : K) (p : Vertex K) : Vertex K :=
  (σ*p.1,![σ*p.2 0,σ*p.2 1,p.2 2])

lemma pointScale_injective (σ : K) (hσ : σ ≠ 0) : Function.Injective (pointScale σ) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun p : Vertex K => p.2 0) h
  have h1 := congrArg (fun p : Vertex K => p.2 1) h
  have h2 := congrArg (fun p : Vertex K => p.2 2) h
  dsimp [pointScale] at hx h0 h1 h2
  refine Prod.ext hx ?_
  funext i
  fin_cases i
  · exact mul_left_cancel₀ hσ h0
  · exact mul_left_cancel₀ hσ h1
  · exact h2

lemma lineScale_injective (σ : K) (hσ : σ ≠ 0) : Function.Injective (lineScale σ) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun p : Vertex K => p.2 0) h
  have h1 := congrArg (fun p : Vertex K => p.2 1) h
  have h2 := congrArg (fun p : Vertex K => p.2 2) h
  dsimp [lineScale] at hx h0 h1 h2
  refine Prod.ext (mul_left_cancel₀ hσ hx) ?_
  funext i
  fin_cases i
  · exact mul_left_cancel₀ hσ h0
  · exact mul_left_cancel₀ hσ h1
  · exact h2

lemma scale_inc (σ : K) (Q : K → K → K) {p l : Vertex K}
    (h : Inc (fun a b => Q (σ*a) (σ*b)) p l) :
    Inc Q (pointScale σ p) (lineScale σ l) := by
  obtain ⟨h0,h1,h2⟩ := h
  dsimp [Inc,pointScale,lineScale]
  refine ⟨?_,?_,h2⟩
  · linear_combination σ*h0
  · linear_combination σ*h1

lemma scale_octagon (σ : K) (hσ : σ ≠ 0) (Q : K → K → K)
    (h : Octagon (fun a b => Q (σ*a) (σ*b))) : Octagon Q := by
  obtain ⟨p,l,hp,hl,h1,h2⟩ := h
  exact ⟨pointScale σ ∘ p,lineScale σ ∘ l,
    (pointScale_injective σ hσ).comp hp,(lineScale_injective σ hσ).comp hl,
    fun i => scale_inc σ Q (h1 i),fun i => scale_inc σ Q (h2 i)⟩

lemma exists_good_shear [Fintype K]
    (A E J L M d e j u w : K) (hd : d ≠ 0) (hu : u ≠ 0) (hL : L ≠ 0)
    (hAE : A ≠ 0 ∨ E ≠ 0) (hq : 6 < Fintype.card K) :
    ∃ τ : K, (A+E*τ^4)*u+E*w ≠ 0 ∧
      (J+L*τ+M*τ^2)*d+L*e+M*j ≠ 0 := by
  let p : Polynomial K := Polynomial.C (A*u+E*w)+Polynomial.C (E*u)*Polynomial.X^4
  let q : Polynomial K := Polynomial.C (J*d+L*e+M*j)+Polynomial.C (L*d)*Polynomial.X+
    Polynomial.C (M*d)*Polynomial.X^2
  have hp : p ≠ 0 := by
    intro he
    by_cases hE : E = 0
    · have hA := hAE.resolve_right (not_not_intro hE)
      have h0 := congrArg (fun p : Polynomial K => p.coeff 0) he
      have hh : A*u = 0 := by simpa [p,hE] using h0
      exact mul_ne_zero hA hu hh
    · have h4 := congrArg (fun p : Polynomial K => p.coeff 4) he
      have hh : E*u = 0 := by
        simpa only [p,Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul_X_pow,
          show (4 : ℕ) ≠ 0 by decide,ite_false,ite_true,zero_add,Polynomial.coeff_zero] using h4
      exact mul_ne_zero hE hu hh
  have hq0 : q ≠ 0 := by
    intro he
    have h1 := congrArg (fun p : Polynomial K => p.coeff 1) he
    have hh : L*d = 0 := by
      norm_num only [q,Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X,Polynomial.coeff_zero,ite_true,ite_false,zero_add,add_zero] at h1
      exact h1
    exact mul_ne_zero hL hd hh
  have hdeg : (p*q).natDegree ≤ 6 := by dsimp [p,q]; compute_degree
  obtain ⟨τ,hτ⟩ := exists_poly_value (p*q) (mul_ne_zero hp hq0) (hdeg.trans_lt hq)
  have hep : p.eval τ = (A+E*τ^4)*u+E*w := by
    simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X]
    ring
  have heq : q.eval τ = (J+L*τ+M*τ^2)*d+L*e+M*j := by
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X]
    ring
  rw [Polynomial.eval_mul,hep,heq] at hτ
  exact ⟨τ,(mul_ne_zero_iff.mp hτ).1,(mul_ne_zero_iff.mp hτ).2⟩

def pure (A E J L M : K) (a b : K) : K :=
  A*a^4+E*b^4+J*a^2+L*a*b+M*b^2

lemma moment_scaled_sheared [CharP K 2]
    (A E J L M u v r t σ τ : K) :
    moment u v r t (fun a b => pure A E J L M (σ*a) (σ*(b+τ*a))) =
      σ^4*((A+E*τ^4)*U u v r t+E*V u v r t)+
      σ^2*((J+L*τ+M*τ^2)*D u v r t+L*Erdos713C8FiniteQuadratic.E u v r t+
        M*Erdos713C8FiniteQuadratic.J u v r t) := by
  have he : (fun a b => pure A E J L M (σ*a) (σ*(b+τ*a))) =
      (fun a b => σ^4*((A+E*τ^4)*a^4+E*b^4)+
        σ^2*((J+L*τ+M*τ^2)*a^2+L*a*b+M*b^2)) := by
    funext a b
    simp only [pure,mul_pow,CharTwo.add_sq,add_four_char_two]
    ring
  rw [he]
  simp only [mul_assoc,moment_add,moment_smul,moment_left_four,moment_right_four,
    moment_left_sq,moment_right_sq,moment_mul]

lemma moment_parallelogram [CharP K 2] (u : K) (Q : K → K → K) :
    moment u (1-u) 1 1 Q = Q 0 0+Q u u+Q 1 u+Q (1-u) 0 := by
  have hS : (1-(1-u))*1-(1-u)*1 = 1 := by
    linear_combination (u-1)*(CharTwo.two_eq_zero (R := K))
  have hT : (1-u)*1-u*1 = 1 := by
    linear_combination -u*(CharTwo.two_eq_zero (R := K))
  have hbu : (1-(1-u))*1 = u := by ring
  dsimp [moment]
  rw [hS,hT,hbu]
  simp only [mul_one,CharTwo.sub_eq_add]

lemma pure_no_mixed [Fintype K] [CharP K 2]
    (A E J M : K) (hq : 4 < Fintype.card K) : Octagon (pure A E J 0 M) := by
  obtain ⟨u,_,_,_,hu,_,hu1,_⟩ := parameters_char_two (K := K) hq
  have huv : u ≠ 1-u := by
    intro he
    have htwo : (2 : K)*u = 1 := by linear_combination he
    exact zero_ne_one (by simpa only [CharTwo.two_eq_zero,zero_mul] using htwo)
  apply octagon_of_moment _ u (1-u) 1 1 hu (sub_ne_zero.mpr hu1.symm) hu1
    (by intro he; apply hu; linear_combination -he) huv one_ne_zero one_ne_zero
  · ring
  · rw [moment_parallelogram]
    simp only [pure,CharTwo.sub_eq_add,add_four_char_two,CharTwo.add_sq,one_pow,zero_pow
      (by decide : 4 ≠ 0),zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,mul_one]
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero]

lemma pure_with_mixed [Fintype K] [CharP K 2]
    (A E J L M : K) (hL : L ≠ 0) (hq : 8 < Fintype.card K) :
    Octagon (pure A E J L M) := by
  by_cases hAE : A ≠ 0 ∨ E ≠ 0
  · obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hd,hU⟩ := fourth_parameters (K := K) hq
    obtain ⟨τ,hk,hl⟩ := exists_good_shear A E J L M
      (D u v r t) (Erdos713C8FiniteQuadratic.E u v r t) (Erdos713C8FiniteQuadratic.J u v r t)
      (U u v r t) (V u v r t) hd hU hL hAE (by omega)
    let k := (A+E*τ^4)*U u v r t+E*V u v r t
    let l := (J+L*τ+M*τ^2)*D u v r t+L*Erdos713C8FiniteQuadratic.E u v r t+
      M*Erdos713C8FiniteQuadratic.J u v r t
    have hSq : Function.Surjective (fun z : K => z^2) :=
      Finite.surjective_of_injective (frobenius_inj K 2)
    obtain ⟨σ,hσ⟩ := hSq (-l/k)
    change σ^2 = -l/k at hσ
    have hσ0 : σ ≠ 0 := by
      intro he
      rw [he,zero_pow (by decide : 2 ≠ 0)] at hσ
      exact (div_ne_zero (neg_ne_zero.mpr hl) hk) hσ.symm
    have hzero : σ^2*k+l = 0 := by
      rw [hσ,div_mul_cancel₀ _ hk]
      ring
    apply scale_octagon σ hσ0
    apply shift_octagon τ (Q := fun a b => pure A E J L M (σ*a) (σ*(b+τ*a)))
    · intro a b; rfl
    · apply octagon_of_moment _ u v r t hu hv hu1 hv1 huv hr ht hB
      rw [moment_scaled_sheared]
      change σ^4*k+σ^2*l=0
      linear_combination σ^2*hzero
  · push_neg at hAE
    rcases hAE with ⟨rfl,rfl⟩
    have he : pure (0 : K) 0 J L M = (fun a b => J*a^2+L*a*b+M*b^2) := by
      funext a b
      simp only [pure,zero_mul,zero_add]
    rw [he]
    exact homogeneous_quadratic_char_two J L M (by omega)

theorem pure_octagon [Fintype K] [CharP K 2]
    (A E J L M : K) (hq : 8 < Fintype.card K) : Octagon (pure A E J L M) := by
  by_cases hL : L = 0
  · subst L
    exact pure_no_mixed A E J M (by omega)
  · exact pure_with_mixed A E J L M hL hq

theorem additive_quartic_octagon [Fintype K] [CharP K 2]
    (A E J L M N O P : K) (hq : 8 < Fintype.card K) :
    Octagon (quartic A 0 0 0 E 0 0 0 0 J L M N O P) := by
  have he : quartic A 0 0 0 E 0 0 0 0 J L M N O P =
      (fun a b => pure A E J L M a b+N*a+O*b+P) := by
    funext a b
    simp only [quartic,cubic,pure,zero_mul,zero_add,add_zero]
    ring
  rw [he]
  exact linear_octagon N O P (pure_octagon A E J L M hq)

#print axioms fourth_parameters
#print axioms scale_octagon
#print axioms exists_good_shear
#print axioms additive_quartic_octagon
end Erdos713C8QuarticAdditive
