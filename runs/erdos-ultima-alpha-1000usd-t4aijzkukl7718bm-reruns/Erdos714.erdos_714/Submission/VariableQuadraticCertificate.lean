import Submission.VariableQuadraticSlice

/-!
A symbolic certificate for the varying quadratic-form graph. It works over
any characteristic-three field with a fixed root of X^3-X+1 and an imaginary
unit negated by the involution. Existence of these parameters in a particular
finite-field family is not asserted here. This does not settle Erdős 714.
-/
noncomputable section
open SimpleGraph
namespace Erdos714VariableQuadratic
variable {E : Type*} [Field E] [CharP E 3]

def scalarRows (a : E) : Fin 4 → E := ![(a-1)^2,-(a-1)^2,a*(a-1),-a*(a-1)]

omit [CharP E 3] in
lemma parameter_ne_zero (a : E) (ha : a^3-a+1 = 0) : a ≠ 0 := by
  intro h
  simp [h] at ha

omit [CharP E 3] in
lemma parameter_ne_one (a : E) (ha : a^3-a+1 = 0) : a ≠ 1 := by
  intro h
  simp [h] at ha

omit [CharP E 3] in
lemma parameter_ne_neg_one (a : E) (ha : a^3-a+1 = 0) : a ≠ -1 := by
  intro h
  norm_num [h] at ha

lemma scalarRows_injective (a : E) (ha : a^3-a+1 = 0) : Function.Injective (scalarRows a) := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have ha0 := parameter_ne_zero a ha
  have ha1 := parameter_ne_one a ha
  have ham := parameter_ne_neg_one a ha
  have hz : a-1 ≠ 0 := sub_ne_zero.mpr ha1
  have hc : (a-1)^2 ≠ 0 := pow_ne_zero _ hz
  have hd : a*(a-1) ≠ 0 := mul_ne_zero ha0 hz
  have h2 : (2 : E) ≠ 0 := by
    intro h
    apply one_ne_zero (α := E)
    linear_combination h3-h
  have hs (x : E) (hx : x ≠ 0) : x ≠ -x := by
    intro h
    apply mul_ne_zero h2 hx
    linear_combination h
  have hsc := hs _ hc
  have hsd := hs _ hd
  have hcd : (a-1)^2 ≠ a*(a-1) := by
    intro h
    have hh : (a-1)*(a-1) = (a-1)*a := by linear_combination h
    have hh' := mul_left_cancel₀ hz hh
    apply one_ne_zero (α := E)
    linear_combination -hh'
  have hcmd : (a-1)^2 ≠ -(a*(a-1)) := by
    intro h
    have hh : (a-1)*(a-1) = (a-1)*(-a) := by linear_combination h
    have hh' := mul_left_cancel₀ hz hh
    apply ham
    linear_combination 2*hh'+(1-a)*h3
  intro j k h
  fin_cases j <;> fin_cases k <;> simp_all [scalarRows, eq_comm, neg_mul]

lemma quartic_at_first (a : E) (ha : a^3-a+1 = 0) : quartic a ((a-1)^2) ((a-1)^2) = 0 := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  unfold quartic
  linear_combination (2*a^5-16*a^4+58*a^3-128*a^2+208*a-290)*ha +
    (130*a^2-172*a+98)*h3

lemma quartic_at_second (a : E) (ha : a^3-a+1 = 0) : quartic a ((a-1)^2) (a*(a-1)) = 0 := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  unfold quartic
  linear_combination (2*a^5-10*a^4+23*a^3-36*a^2+48*a-61)*ha +
    (28*a^2-37*a+21)*h3

lemma open_first (a : E) (ha : a^3-a+1 = 0) : ((a-1)^2)^2+a^2 ≠ 1 := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have hh : (((a-1)^2)^2+a^2-1)*a = 1 := by
    linear_combination (a^2-4*a+8)*ha + (-3*a^2+4*a-3)*h3
  intro h
  rw [h, sub_self, zero_mul] at hh
  exact zero_ne_one hh

lemma open_second (a : E) (ha : a^3-a+1 = 0) : (a*(a-1))^2+a^2 ≠ 1 := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have hh : (a*(a-1))^2+a^2-1 = 1 := by
    linear_combination (a-2)*ha + (a^2-a)*h3
  intro h
  rw [h, sub_self] at hh
  exact zero_ne_one hh

omit [CharP E 3] in
lemma quartic_neg (b c t : E) : quartic b c (-t) = quartic b c t := by
  unfold quartic
  ring

/-- Every algebraic and distinctness condition of the quartic rectangle is
now discharged in terms of the two displayed extension parameters. -/
def cubicParameterCopy (τ : E →+* E) (hτ : Function.Involutive τ)
    (a i : E) (ha : a^3-a+1 = 0) (hτa : τ a = a)
    (hi : i^2 = -1) (hτi : τ i = -i) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph τ) := by
  apply quarticCopy τ hτ i a ((a-1)^2) hi hτi hτa (by simp [hτa])
    (parameter_ne_zero a ha) (pow_ne_zero _ (sub_ne_zero.mpr (parameter_ne_one a ha)))
    ⟨scalarRows a,scalarRows_injective a ha⟩
  · intro j
    fin_cases j <;> simp [scalarRows, hτa]
  · intro j
    have h₁ := open_first a ha
    have h₂ := open_second a ha
    fin_cases j <;> simpa [scalarRows] using (by first | exact h₁ | exact h₂)
  · intro j
    have h₁ := quartic_at_first a ha
    have h₂ := quartic_at_second a ha
    fin_cases j <;> first
      | simpa [scalarRows, quartic_neg, neg_mul] using h₁
      | simpa [scalarRows, quartic_neg, neg_mul] using h₂

theorem cubic_parameter_not_free (τ : E →+* E) (hτ : Function.Involutive τ)
    (a i : E) (ha : a^3-a+1 = 0) (hτa : τ a = a)
    (hi : i^2 = -1) (hτi : τ i = -i) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph τ) := by
  intro h
  exact h ⟨cubicParameterCopy τ hτ a i ha hτa hi hτi⟩

#print axioms scalarRows_injective
#print axioms quartic_at_first
#print axioms quartic_at_second
#print axioms open_first
#print axioms open_second
#print axioms cubicParameterCopy
#print axioms cubic_parameter_not_free
end Erdos714VariableQuadratic
