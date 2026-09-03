import FormalConjecturesUtil

/-!
A uniform limitation of the proposed Ree-axis root argument. If sigma squared
is cubing in characteristic three, and the field has more than three elements,
a nonzero linear combination of 1, X, X^2, sigma(X) has four distinct roots.
This concerns a root-count ingredient, not arbitrary graphs or Erdős 714.
-/

noncomputable section
open Classical
set_option maxHeartbeats 4000000

namespace Erdos714ReeAxis

variable {F : Type*} [Field F] [CharP F 3]
variable (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x^3)

omit [CharP F 3] in
lemma nonfixed_ne_zero {t : F} (ht : σ t ≠ t) : t ≠ 0 := by
  intro he
  subst t
  exact ht (map_zero σ)

omit [CharP F 3] in
lemma nonfixed_ne_one {t : F} (ht : σ t ≠ t) : t ≠ 1 := by
  intro he
  subst t
  exact ht (map_one σ)

include hσ in
omit [CharP F 3] in
lemma cube_ne {t : F} (ht : σ t ≠ t) : σ t ≠ t^3 := by
  intro he
  apply ht
  apply σ.injective
  exact (hσ t).trans he.symm

include hσ in
omit [CharP F 3] in
lemma square_ne {t : F} (ht : σ t ≠ t) : σ t ≠ t^2 := by
  intro he
  have hh := congrArg σ he
  rw [hσ, map_pow, he] at hh
  have hz : t^3*(t-1) = 0 := by linear_combination -hh
  exact mul_ne_zero (pow_ne_zero 3 (nonfixed_ne_zero σ ht))
    (sub_ne_zero.mpr (nonfixed_ne_one σ ht)) hz

include hσ in
lemma second_factor_ne {t : F} (ht : σ t ≠ t) : t^2+t+σ t ≠ 0 := by
  intro h
  have hs := congrArg σ h
  simp only [map_add, map_pow, map_zero, hσ] at hs
  have hz : t*(t-1)^3 = 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!))
      hs - (σ t-t^2-t+1)*h
  exact mul_ne_zero (nonfixed_ne_zero σ ht)
    (pow_ne_zero 3 (sub_ne_zero.mpr (nonfixed_ne_one σ ht))) hz

include hσ in
lemma third_factor_ne {t : F} (ht : σ t ≠ t) : t^2+t*σ t+σ t ≠ 0 := by
  intro h
  have hs := congrArg σ h
  simp only [map_add, map_mul, map_pow, map_zero, hσ] at hs
  have hz : t^3*(t-1)^3 = 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!))
      ((t+1)*σ t+(t+1)*t^3-t^2)*h - (t+1)^2*hs
  exact mul_ne_zero (pow_ne_zero 3 (nonfixed_ne_zero σ ht))
    (pow_ne_zero 3 (sub_ne_zero.mpr (nonfixed_ne_one σ ht))) hz

/-- The fourth point completing the three roots 0, 1, t. -/
def fourth (t : F) : F :=
  -((t-1)*(σ t-t^2)*((σ t)^2-t^3))/((σ t-t)^2*(σ t-t^3))

include hσ in
omit [CharP F 3] in
lemma denominator_ne {t : F} (ht : σ t ≠ t) :
    (σ t-t)^2*(σ t-t^3) ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr ht)) (sub_ne_zero.mpr (cube_ne σ hσ ht))

include hσ in
omit [CharP F 3] in
lemma fourth_ne_zero {t : F} (ht : σ t ≠ t) : fourth σ t ≠ 0 := by
  have hh : (σ t)^2-t^3 ≠ 0 := by
    have he := σ.injective.ne (square_ne σ hσ ht)
    apply sub_ne_zero.mpr
    exact (show t^3 ≠ (σ t)^2 by simpa only [map_pow,hσ] using he).symm
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (nonfixed_ne_one σ ht))
      (sub_ne_zero.mpr (square_ne σ hσ ht))) hh)) (denominator_ne σ hσ ht)

include hσ in
lemma fourth_sub_one {t : F} (ht : σ t ≠ t) :
    fourth σ t - 1 =
      -(t*(t^2+t+σ t)*(t^3+(σ t)^2+σ t))/((σ t-t)^2*(σ t-t^3)) := by
  apply (eq_div_iff (denominator_ne σ hσ ht)).mpr
  rw [sub_mul, fourth, div_mul_cancel₀ _ (denominator_ne σ hσ ht)]
  ring_nf
  reduce_mod_char!
  ring

include hσ in
lemma fourth_ne_one {t : F} (ht : σ t ≠ t) : fourth σ t ≠ 1 := by
  apply sub_ne_zero.mp
  rw [fourth_sub_one σ hσ ht]
  have hh : t^3+(σ t)^2+σ t ≠ 0 := by
    have he := σ.injective.ne (second_factor_ne σ hσ ht)
    simpa only [map_add,map_pow,map_zero,hσ,add_assoc,add_comm,add_left_comm] using he
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (nonfixed_ne_zero σ ht) (second_factor_ne σ hσ ht)) hh))
    (denominator_ne σ hσ ht)

include hσ in
lemma fourth_sub_self {t : F} (ht : σ t ≠ t) :
    fourth σ t - t =
      ((t^2+t*σ t+σ t)*(t^3*σ t+t^3+(σ t)^2))/((σ t-t)^2*(σ t-t^3)) := by
  apply (eq_div_iff (denominator_ne σ hσ ht)).mpr
  rw [sub_mul, fourth, div_mul_cancel₀ _ (denominator_ne σ hσ ht)]
  ring_nf
  reduce_mod_char!
  ring_nf
  reduce_mod_char!

include hσ in
lemma fourth_ne_self {t : F} (ht : σ t ≠ t) : fourth σ t ≠ t := by
  apply sub_ne_zero.mp
  rw [fourth_sub_self σ hσ ht]
  have hh : t^3*σ t+t^3+(σ t)^2 ≠ 0 := by
    have he := σ.injective.ne (third_factor_ne σ hσ ht)
    simpa only [map_add,map_mul,map_pow,map_zero,hσ,add_assoc,add_comm,add_left_comm,mul_comm] using he
  exact div_ne_zero (mul_ne_zero (third_factor_ne σ hσ ht) hh) (denominator_ne σ hσ ht)

/-- A denominator-free root equation for the four points. -/
def equation (t z : F) : F :=
  (σ t-t)*z^2 + (t^2-σ t)*z - t*(t-1)*σ z

omit [CharP F 3] in
lemma zero_root (t : F) : equation σ t 0 = 0 := by simp [equation]
omit [CharP F 3] in
lemma one_root (t : F) : equation σ t 1 = 0 := by simp only [equation,map_one]; ring
omit [CharP F 3] in
lemma self_root (t : F) : equation σ t t = 0 := by dsimp [equation]; ring

include hσ in
lemma fourth_root {t : F} (ht : σ t ≠ t) : equation σ t (fourth σ t) = 0 := by
  have h₁ : σ t-t ≠ 0 := sub_ne_zero.mpr ht
  have h₂ : σ t-t^3 ≠ 0 := sub_ne_zero.mpr (cube_ne σ hσ ht)
  have h₃ : t^3-σ t ≠ 0 := sub_ne_zero.mpr (cube_ne σ hσ ht).symm
  have h₄ : t^3-(σ t)^3 ≠ 0 := by
    have he := σ.injective.ne h₂
    simpa only [map_sub,map_pow,map_zero,hσ] using he
  simp only [equation,fourth,map_div₀,map_neg,map_sub,map_mul,map_pow,map_one,hσ]
  field_simp [h₁,h₂,h₃,h₄]
  ring_nf
  reduce_mod_char!

/-- Both distinctness and all four original semilinear equations are explicit. -/
def rootEmbedding (hσ : ∀ x, σ (σ x) = x^3) (t : F) (ht : σ t ≠ t) : Fin 4 ↪ F where
  toFun := ![0,1,t,fourth σ t]
  inj' := by
    have ht0 := nonfixed_ne_zero σ ht
    have ht1 := nonfixed_ne_one σ ht
    have hw0 := fourth_ne_zero σ hσ ht
    have hw1 := fourth_ne_one σ hσ ht
    have hwt := fourth_ne_self σ hσ ht
    intro i j he
    fin_cases i <;> fin_cases j <;>
      simp [ht0,ht1,hw0,hw1,hwt,ht0.symm,ht1.symm,hw0.symm,hw1.symm,hwt.symm] at he ⊢

include hσ in
lemma embedding_roots (t : F) (ht : σ t ≠ t) (i : Fin 4) :
    equation σ t (rootEmbedding σ hσ t ht i) = 0 := by
  fin_cases i
  · exact zero_root σ t
  · exact one_root σ t
  · exact self_root σ t
  · exact fourth_root σ hσ ht

include hσ in
omit [CharP F 3] in
lemma fixed_trichotomy {t : F} (ht : σ t = t) : t = 0 ∨ t = 1 ∨ t = -1 := by
  have he : t^3 = t := by rw [← hσ t,ht,ht]
  have hz : t*(t-1)*(t+1) = 0 := by linear_combination he
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

variable [Fintype F]

include hσ in
omit [CharP F 3] in
lemma exists_nonfixed (hq : 3 < Fintype.card F) : ∃ t : F, σ t ≠ t := by
  by_contra! h
  have hs : (Finset.univ : Finset F) ⊆ {0,1,-1} := by
    intro t _
    rcases fixed_trichotomy σ hσ (h t) with rfl | rfl | rfl <;> simp
  have hc := (Finset.card_le_card hs).trans Finset.card_le_three
  simp only [Finset.card_univ] at hc
  omega

include hσ in
/-- The four-root obstruction is uniform over all fields with the displayed twist. -/
theorem exists_four_roots (hq : 3 < Fintype.card F) :
    ∃ a b c d : F, c ≠ 0 ∧ ∃ f : Fin 4 ↪ F,
      ∀ i, c*(f i)^2+d*σ (f i)+a*f i+b = 0 := by
  obtain ⟨t,ht⟩ := exists_nonfixed σ hσ hq
  refine ⟨t^2-σ t,0,σ t-t,-t*(t-1),sub_ne_zero.mpr ht,rootEmbedding σ hσ t ht,?_⟩
  intro i
  have he := embedding_roots σ hσ t ht i
  dsimp [equation] at he
  linear_combination he

/-- Applying the twist once more gives an actual quartic eliminant. -/
def eliminant (a b c d : F) : Polynomial F :=
  Polynomial.C (σ c*c^2)*Polynomial.X^4 +
  Polynomial.C (2*σ c*c*a+σ d*d^2)*Polynomial.X^3 +
  Polynomial.C (σ c*(a^2+2*c*b)-σ a*d*c)*Polynomial.X^2 +
  Polynomial.C (2*σ c*a*b-σ a*d*a)*Polynomial.X +
  Polynomial.C (σ c*b^2-σ a*d*b+σ b*d^2)

omit [CharP F 3] [Fintype F] in
lemma eliminant_degree (a b c d : F) : (eliminant σ a b c d).natDegree ≤ 4 := by
  unfold eliminant
  compute_degree!

omit [CharP F 3] [Fintype F] in
lemma eliminant_ne_zero (a b c d : F) (hc : c ≠ 0) : eliminant σ a b c d ≠ 0 := by
  intro he
  have hh := congrArg (fun p : Polynomial F => p.coeff 4) he
  simp only [eliminant,Polynomial.coeff_add,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_X,Polynomial.coeff_C,Polynomial.coeff_zero] at hh
  norm_num at hh
  exact hc hh

include hσ in
omit [CharP F 3] [Fintype F] in
lemma eliminant_root (a b c d z : F) (hz : c*z^2+d*σ z+a*z+b=0) :
    (eliminant σ a b c d).eval z = 0 := by
  have hs := congrArg σ hz
  simp only [map_add,map_mul,map_pow,map_zero,hσ] at hs
  simp only [eliminant,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X]
  linear_combination d^2*hs+(σ c*(c*z^2+a*z+b-d*σ z)-σ a*d)*hz

include hσ in
omit [CharP F 3] [Fintype F] in
/-- The bound four is valid; the preceding construction shows that three is not. -/
theorem root_bound_four (a b c d : F) (hc : c ≠ 0) (S : Finset F)
    (hS : ∀ z ∈ S, c*z^2+d*σ z+a*z+b=0) : S.card ≤ 4 := by
  have hsub : S ⊆ (eliminant σ a b c d).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset,Polynomial.mem_roots (eliminant_ne_zero σ a b c d hc)]
    exact eliminant_root σ hσ a b c d z (hS z hz)
  calc
    S.card ≤ (eliminant σ a b c d).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (eliminant σ a b c d).roots.card := Multiset.toFinset_card_le _
    _ ≤ (eliminant σ a b c d).natDegree := Polynomial.card_roots' _
    _ ≤ 4 := eliminant_degree σ a b c d

/-- The actual Frobenius twist in every odd-degree ternary finite field. -/
def reeTwist (m : ℕ) : F →+* F := iterateFrobenius F 3 (m+1)

lemma reeTwist_square (m : ℕ) (hcard : Fintype.card F = 3^(2*m+1)) (x : F) :
    reeTwist (F := F) m (reeTwist m x) = x^3 := by
  change (x^(3^(m+1)))^(3^(m+1)) = x^3
  rw [← pow_mul,← pow_add]
  rw [show m+1+(m+1)=2*m+1+1 by omega, Nat.pow_succ, pow_mul, ← hcard]
  rw [FiniteField.pow_card]

/-- In particular, every ternary Ree field of order at least 27 has the obstruction. -/
theorem finite_four_roots (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card F = 3^(2*m+1)) :
    ∃ a b c d : F, c ≠ 0 ∧ ∃ f : Fin 4 ↪ F,
      ∀ i, c*(f i)^2+d*reeTwist m (f i)+a*f i+b=0 := by
  apply exists_four_roots (reeTwist m) (reeTwist_square m hcard)
  rw [hcard]
  exact (show 3^1=3 by norm_num) ▸
    Nat.pow_lt_pow_right (by decide : 1 < 3) (by omega : 1 < 2*m+1)

end Erdos714ReeAxis

#print axioms Erdos714ReeAxis.fourth_root
#print axioms Erdos714ReeAxis.rootEmbedding
#print axioms Erdos714ReeAxis.exists_four_roots

#print axioms Erdos714ReeAxis.root_bound_four
#print axioms Erdos714ReeAxis.finite_four_roots
