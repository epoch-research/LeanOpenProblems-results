import FormalConjecturesUtil

/-! Rational parametrization and a finite-field lower bound for a nonsingular
binary quadratic level set. This is an auxiliary construction lemma. -/

noncomputable section
open Polynomial Classical

namespace Erdos714BinaryConic
variable {F : Type*} [Field F]

def normPair (δ : F) (p : F × F) : F := p.1^2-δ*p.2^2

def circlePoint (δ t : F) : F × F :=
  ((1+δ*t^2)/(1-δ*t^2), 2*t/(1-δ*t^2))

lemma circlePoint_norm (δ t : F) (ht : 1-δ*t^2 ≠ 0) :
    normPair δ (circlePoint δ t) = 1 := by
  dsimp [normPair, circlePoint]
  field_simp
  ring

lemma circlePoint_recover (h₂ : (2 : F) ≠ 0) (δ t : F) (ht : 1-δ*t^2 ≠ 0) :
    (circlePoint δ t).2/((circlePoint δ t).1+1) = t := by
  dsimp [circlePoint]
  have hd : (1+δ*t^2)/(1-δ*t^2)+1 = 2/(1-δ*t^2) := by field_simp; ring
  rw [hd]
  field_simp
  simpa only [mul_comm δ] using mul_div_cancel_right₀ t ht

lemma circlePoint_injective (h₂ : (2 : F) ≠ 0) (δ : F) :
    Function.Injective (fun t : {t : F // 1-δ*t^2 ≠ 0} => circlePoint δ t.val) := by
  intro t u h
  have hh := congrArg (fun p : F × F => p.2/(p.1+1)) h
  apply Subtype.ext
  simpa only [circlePoint_recover h₂ δ t.val t.property,
    circlePoint_recover h₂ δ u.val u.property] using hh

variable [Fintype F]

lemma parameter_card (δ : F) :
    Fintype.card F ≤ Fintype.card {t : F // 1-δ*t^2 ≠ 0}+2 := by
  let p : F[X] := 1-C δ*X^2
  have hp : p ≠ 0 := by
    intro hz
    have hh := congrArg (Polynomial.eval 0) hz
    simp [p] at hh
  have hd : p.natDegree ≤ 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have hb : (Finset.univ.filter (fun t : F => 1-δ*t^2=0)).card ≤ 2 := by
    have hh := Polynomial.card_le_degree_of_subset_roots (p := p)
      (Z := Finset.univ.filter (fun t : F => 1-δ*t^2=0))
      (fun t ht => (Polynomial.mem_roots hp).mpr (by
        simpa [p] using (Finset.mem_filter.mp ht).2))
    exact_mod_cast hh.trans hd
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
    (p := fun t => 1-δ*t^2=0)
  simp only [Finset.card_univ] at hh
  rw [Fintype.card_subtype]
  simp only [ne_eq]
  omega

lemma exists_pair (h₂ : (2 : F) ≠ 0) {δ γ : F} (hδ : δ ≠ 0) :
    ∃ p : F × F, normPair δ p = γ := by
  have hc : ringChar F ≠ 2 := by
    intro he
    have hh : (ringChar F : F) = 0 := CharP.cast_eq_zero F (ringChar F)
    exact h₂ (by simpa only [he, Nat.cast_ofNat] using hh)
  obtain ⟨u,v,h⟩ := FiniteField.exists_root_sum_quadratic
    (f := X^2-C γ) (g := C (-δ)*X^2)
    (Polynomial.degree_X_pow_sub_C (by decide) γ)
    (by rw [Polynomial.degree_C_mul (neg_ne_zero.mpr hδ)]; exact Polynomial.degree_X_pow 2)
    (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨(u,v), ?_⟩
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at h
  dsimp [normPair]
  linear_combination h

def transport (δ : F) (p z : F × F) : F × F :=
  (p.1*z.1+δ*p.2*z.2, p.2*z.1+p.1*z.2)

omit [Fintype F] in
lemma transport_norm (δ : F) (p z : F × F) :
    normPair δ (transport δ p z) = normPair δ p*normPair δ z := by
  dsimp [normPair, transport]
  ring

omit [Fintype F] in
lemma transport_injective {δ : F} {p : F × F} (hp : normPair δ p ≠ 0) :
    Function.Injective (transport δ p) := by
  intro u v h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [transport] at h₁ h₂
  have h₃ : normPair δ p*(u.1-v.1)=0 := by
    dsimp [normPair]
    linear_combination p.1*h₁-δ*p.2*h₂
  have h₄ : normPair δ p*(u.2-v.2)=0 := by
    dsimp [normPair]
    linear_combination -p.2*h₁+p.1*h₂
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h₃).resolve_left hp))
    (sub_eq_zero.mp ((mul_eq_zero.mp h₄).resolve_left hp))

/-- A binary quadratic form with nonzero leading coefficient and discriminant
has at least `|F|-2` points on its level-one conic. -/
theorem quadratic_level_card (h₂ : (2 : F) ≠ 0) (a b c : F)
    (ha : a ≠ 0) (hΔ : b^2-4*a*c ≠ 0) :
    Fintype.card F ≤ Fintype.card {p : F × F // a*p.1^2+b*p.1*p.2+c*p.2^2=1}+2 := by
  let δ := b^2-4*a*c
  obtain ⟨p,hp⟩ := exists_pair h₂ (γ := 4*a) hΔ
  have h4a : 4*a ≠ 0 := by
    have h4 : (4 : F) = 2*2 := by ring
    rw [h4]
    exact mul_ne_zero (mul_ne_zero h₂ h₂) ha
  have hn : normPair δ p ≠ 0 := by change normPair (b^2-4*a*c) p ≠ 0; rw [hp]; exact h4a
  let f (t : {t : F // 1-δ*t^2 ≠ 0}) : F × F :=
    let w := transport δ p (circlePoint δ t.val)
    ((w.1-b*w.2)/(2*a), w.2)
  have hf (t) : a*(f t).1^2+b*(f t).1*(f t).2+c*(f t).2^2=1 := by
    have hh := transport_norm δ p (circlePoint δ t.val)
    rw [hp, circlePoint_norm _ _ t.property, mul_one] at hh
    dsimp [f]
    field_simp
    dsimp [normPair, δ] at hh
    linear_combination hh
  let e : {t : F // 1-δ*t^2 ≠ 0} ↪ {p : F × F // a*p.1^2+b*p.1*p.2+c*p.2^2=1} :=
    ⟨fun t => ⟨f t,hf t⟩, by
      intro t u he
      have hh : f t=f u := congrArg Subtype.val he
      have h₁ := congrArg Prod.fst hh
      have h₂' := congrArg Prod.snd hh
      dsimp [f] at h₁ h₂'
      apply circlePoint_injective h₂ δ
      apply transport_injective hn
      apply Prod.ext ?_ h₂'
      have h₃ := (div_left_inj' (mul_ne_zero h₂ ha)).mp h₁
      linear_combination h₃+b*h₂'⟩
  exact (parameter_card δ).trans (Nat.add_le_add_right (Fintype.card_le_of_injective e e.injective) 2)

end Erdos714BinaryConic
#print axioms Erdos714BinaryConic.quadratic_level_card
