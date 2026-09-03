import FormalConjecturesUtil

/-! Scalar exclusions for a rational twisted-central octagon word. -/
namespace Erdos713C8SuzukiScalarExclusions
variable {F : Type*} [Field F] [CharP F 2]
set_option maxHeartbeats 2000000

lemma pow_eight_of_J_zero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (h : c^2+c+σ c=0) : c^8=c := by
  have hC : σ c=c^2+c := (CharTwo.add_eq_zero.mp h).symm
  have hh := congrArg σ h
  simp only [map_add,map_pow,hσ] at hh
  rw [map_zero,hC] at hh
  have h4 : c^4+c^2+c=0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hh
  have hs := congrArg (fun x : F => x^2) h4
  linear_combination (norm := (ring_nf; reduce_mod_char!)) hs-h4

lemma J_ne_zero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc : c^8 ≠ c) : c^2+c+σ c ≠ 0 :=
  fun h => hc (pow_eight_of_J_zero σ hσ c h)

omit [CharP F 2] in
lemma c_ne_zero {c : F} (hc : c^8 ≠ c) : c ≠ 0 := by
  intro h; subst c; exact hc (by simp)

omit [CharP F 2] in
lemma c_ne_one {c : F} (hc : c^8 ≠ c) : c ≠ 1 := by
  intro h; subst c; exact hc (by simp)

lemma A_ne_zero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc : c^8 ≠ c) : c^2+c*σ c+σ c ≠ 0 := by
  intro h
  have hc0 := c_ne_zero hc
  have hC0 : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
  have hinv : (c⁻¹)^2+c⁻¹+σ (c⁻¹)=0 := by
    rw [map_inv₀]
    field_simp
    linear_combination h
  have he := pow_eight_of_J_zero σ hσ (c⁻¹) hinv
  apply hc
  apply inv_injective
  simpa only [inv_pow] using he

lemma first_sum_ne_zero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc : c ≠ 0) (hc1 : c ≠ 1) : c+σ c ≠ 0 := by
  intro h
  have he : σ c=c := (CharTwo.add_eq_zero.mp h).symm
  have hh := congrArg σ he
  rw [hσ,he] at hh
  have hfac : c*(c-1)=0 := by linear_combination hh
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exact hc h0
  · exact hc1 (sub_eq_zero.mp h1)

lemma second_sum_ne_zero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc : c ≠ 0) (hc1 : c ≠ 1) : c^2+σ c ≠ 0 := by
  intro h
  have hh := congrArg σ h
  simp only [map_add,map_pow,map_zero,hσ] at hh
  have hs : (c+σ c)^2=0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hh
  exact first_sum_ne_zero σ hσ c hc hc1 (eq_zero_of_pow_eq_zero hs)

omit [CharP F 2] in
lemma exists_parameter [Fintype F] (hq : 8 < Fintype.card F) :
    ∃ c : F, c^8 ≠ c := by
  classical
  let p : Polynomial F := Polynomial.X^8-Polynomial.X
  have hd : p.natDegree=8 := FiniteField.X_pow_card_sub_X_natDegree_eq F (by decide)
  have hp : p ≠ 0 := by
    intro h
    rw [h,Polynomial.natDegree_zero] at hd
    norm_num at hd
  obtain ⟨c,hc⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card p hp
    (by simpa only [hd,Cardinal.mk_fintype,Nat.cast_lt] using hq)
  refine ⟨c,?_⟩
  simpa [p,sub_ne_zero] using hc


end Erdos713C8SuzukiScalarExclusions
