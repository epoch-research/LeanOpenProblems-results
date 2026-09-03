import Submission.OrderMixtureCriterion

/-! Every cover majorant normalized on the singleton patterns is a uniform
mixture of nonnegative normalized first-hit sums, using one order for each final
coordinate. This is a representability theorem, not an objective estimate. -/
namespace Erdos970.FiniteSelberg
open Finset

noncomputable def nonemptyHit {n : ℕ} (v : Fin n → Bool) : ℝ :=
  if v = (fun _ => false) then 0 else 1

noncomputable def prefixAvoid {n : ℕ} (e : Equiv.Perm (Fin n))
    (i : Fin n) (v : Fin n → Bool) : ℝ :=
  if ∀ l, l < i → v (e l) = false then 1 else 0

lemma prefixAvoid_nonneg {n : ℕ} (e : Equiv.Perm (Fin n))
    (i : Fin n) (v : Fin n → Bool) : 0 ≤ prefixAvoid e i v := by
  unfold prefixAvoid
  split_ifs <;> norm_num

lemma prefixAvoid_empty {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    prefixAvoid e i (fun _ => false) = 1 := by simp [prefixAvoid]

lemma prefixAvoid_dependent {n : ℕ} (e : Equiv.Perm (Fin n)) :
    PrefixDependent e (prefixAvoid e) := by
  classical
  intro i v u h
  have he : (∀ l, l < i → v (e l) = false) ↔ (∀ l, l < i → u (e l) = false) := by
    constructor
    · intro hv l hl
      rw [← h l hl]
      exact hv l hl
    · intro hu l hl
      rw [h l hl]
      exact hu l hl
  simp only [prefixAvoid, he]

lemma orderedHitValue_prefixAvoid {n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin n → Bool) : orderedHitValue e (prefixAvoid e) v = nonemptyHit v := by
  classical
  by_cases hv : v = (fun _ => false)
  · subst v
    simp [orderedHitValue, nonemptyHit]
  · let B := univ.filter (fun i => v (e i) = true)
    have hBn : B.Nonempty := by
      by_contra h
      apply hv
      funext j
      cases hj : v j
      · rfl
      · exact False.elim (h ⟨e.symm j, by simp [B, hj]⟩)
    let i := B.min' hBn
    have hi : v (e i) = true := (mem_filter.mp (B.min'_mem hBn)).2
    have hprior (l : Fin n) (hl : l < i) : v (e l) = false := by
      cases hh : v (e l)
      · rfl
      · exact False.elim ((not_lt_of_ge (B.min'_le l (by simp [B, hh]))) hl)
    rw [orderedHitValue, sum_eq_single i]
    · simp only [prefixAvoid, if_pos hprior, hi, if_true, one_mul, nonemptyHit, if_neg hv]
    · intro l hl hli
      by_cases hli' : l < i
      · simp [hprior l hli']
      · have hil : i < l := lt_of_le_of_ne (le_of_not_gt hli') (Ne.symm hli)
        have hn : ¬∀ a, a < l → v (e a) = false := by
          intro h
          have hh := h i hil
          rw [hi] at hh
          exact Bool.noConfusion hh
        simp [prefixAvoid, hn]
    · simp

noncomputable def firstIndicator {n : ℕ} (j : Fin n) (v : Fin n → Bool) : ℝ :=
  (if v j then 1 else 0) * prefixAvoid (Equiv.refl _) j v

lemma firstIndicator_sum {n : ℕ} (v : Fin n → Bool) :
    (∑ j, firstIndicator j v) = nonemptyHit v :=
  orderedHitValue_prefixAvoid (Equiv.refl _) v

lemma firstIndicator_nonneg {n : ℕ} (j : Fin n) (v : Fin n → Bool) :
    0 ≤ firstIndicator j v := by
  apply mul_nonneg _ (prefixAvoid_nonneg _ _ _)
  split_ifs <;> norm_num

noncomputable def gatedExcess {n : ℕ} (F : (Fin n → Bool) → ℝ)
    (j : Fin n) (v : Fin n → Bool) : ℝ := firstIndicator j v * (F v - 1)

lemma gatedExcess_nonneg {n : ℕ} (F : (Fin n → Bool) → ℝ)
    (hF : ∀ v, v ≠ (fun _ => false) → 1 ≤ F v) (j : Fin n) (v : Fin n → Bool) :
    0 ≤ gatedExcess F j v := by
  classical
  by_cases hv : v = (fun _ => false)
  · subst v
    simp [gatedExcess, firstIndicator]
  · exact mul_nonneg (firstIndicator_nonneg j v) (sub_nonneg.mpr (hF v hv))

lemma gatedExcess_sum {n : ℕ} (F : (Fin n → Bool) → ℝ) (v : Fin n → Bool) :
    (∑ j, gatedExcess F j v) = nonemptyHit v * (F v - 1) := by
  simp only [gatedExcess, ← sum_mul, firstIndicator_sum]

noncomputable def finalOrder {n : ℕ} (j : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  Equiv.swap (Fin.last n) j

lemma finalOrder_last {n : ℕ} (j : Fin (n+1)) : finalOrder j (Fin.last n) = j := by
  simp [finalOrder]

lemma update_final_eq {n : ℕ} (j : Fin (n+1)) (v u : Fin (n+1) → Bool)
    (h : ∀ l, l < Fin.last n → v (finalOrder j l) = u (finalOrder j l)) :
    Function.update v j true = Function.update u j true := by
  classical
  funext a
  by_cases ha : a = j
  · subst a
    simp only [Function.update_self]
  · have hl : (finalOrder j).symm a < Fin.last n := by
      apply lt_of_le_of_ne (Fin.le_last _)
      intro he
      apply ha
      calc
        a = finalOrder j ((finalOrder j).symm a) := ((finalOrder j).apply_symm_apply a).symm
        _ = finalOrder j (Fin.last n) := by rw [he]
        _ = j := finalOrder_last j
    simpa [ha] using h ((finalOrder j).symm a) hl

noncomputable def mixtureStage {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ)
    (j i : Fin (n+1)) (v : Fin (n+1) → Bool) : ℝ :=
  prefixAvoid (finalOrder j) i v +
    if i = Fin.last n then (n+1 : ℝ) * gatedExcess F j (Function.update v j true) else 0

lemma mixtureStage_nonneg {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ)
    (hF : ∀ v, v ≠ (fun _ => false) → 1 ≤ F v)
    (j i : Fin (n+1)) (v : Fin (n+1) → Bool) : 0 ≤ mixtureStage F j i v := by
  apply add_nonneg (prefixAvoid_nonneg _ _ _)
  split_ifs
  · exact mul_nonneg (by positivity) (gatedExcess_nonneg F hF j _)
  · rfl

lemma mixtureStage_normalized {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ)
    (hsingle : ∀ j, F (Function.update (fun _ => false) j true) = 1)
    (j i : Fin (n+1)) : mixtureStage F j i (fun _ => false) = 1 := by
  simp [mixtureStage, prefixAvoid_empty, gatedExcess, hsingle]

lemma mixtureStage_dependent {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ)
    (j : Fin (n+1)) : PrefixDependent (finalOrder j) (mixtureStage F j) := by
  classical
  intro i v u h
  have hp := prefixAvoid_dependent (finalOrder j) i v u h
  unfold mixtureStage
  rw [hp]
  by_cases hi : i = Fin.last n
  · subst i
    rw [update_final_eq j v u h]
  · simp [hi]

lemma mixtureStage_value {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ)
    (j : Fin (n+1)) (v : Fin (n+1) → Bool) :
    orderedHitValue (finalOrder j) (mixtureStage F j) v =
      nonemptyHit v + (n+1 : ℝ) * gatedExcess F j v := by
  classical
  have hsum : (∑ i : Fin (n+1), (if v (finalOrder j i) then (1 : ℝ) else 0) *
      (if i = Fin.last n then (n+1 : ℝ) *
        gatedExcess F j (Function.update v j true) else 0)) =
      (n+1 : ℝ) * gatedExcess F j v := by
    rw [sum_eq_single (Fin.last n)]
    · rw [if_pos rfl, finalOrder_last]
      cases hv : v j
      · simp [hv, gatedExcess, firstIndicator]
      · have hu : Function.update v j true = v := by rw [← hv, Function.update_eq_self]
        simp [hu]
    · intro i hi hne
      simp [hne]
    · simp
  unfold orderedHitValue mixtureStage
  simp only [mul_add, sum_add_distrib]
  rw [hsum, ← orderedHitValue, orderedHitValue_prefixAvoid]

/-- Uniform averaging over all possible final coordinates represents every
majorant with zero empty value and singleton values one. -/
theorem normalized_cover_is_order_mixture {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ)
    (hempty : F (fun _ => false) = 0)
    (hcover : ∀ v, v ≠ (fun _ => false) → 1 ≤ F v)
    (hsingle : ∀ j, F (Function.update (fun _ => false) j true) = 1) :
    ∃ (e : Fin (n+1) → Equiv.Perm (Fin (n+1)))
      (W : Fin (n+1) → Fin (n+1) → (Fin (n+1) → Bool) → ℝ),
      (∀ j i v, 0 ≤ W j i v) ∧
      (∀ j i, W j i (fun _ => false) = 1) ∧
      (∀ j, PrefixDependent (e j) (W j)) ∧
      ∀ v, F v = ∑ j, (1 / (n+1 : ℝ)) * orderedHitValue (e j) (W j) v := by
  classical
  refine ⟨finalOrder, mixtureStage F, mixtureStage_nonneg F hcover,
    mixtureStage_normalized F hsingle, mixtureStage_dependent F, ?_⟩
  intro v
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  simp_rw [mixtureStage_value, mul_add]
  rw [sum_add_distrib]
  have hs : (∑ j : Fin (n+1), (1 / (n+1 : ℝ)) * nonemptyHit v) = nonemptyHit v := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    field_simp
  rw [hs]
  have he : (∑ j : Fin (n+1), (1 / (n+1 : ℝ)) * ((n+1 : ℝ) * gatedExcess F j v)) =
      ∑ j : Fin (n+1), gatedExcess F j v := by
    apply sum_congr rfl
    intro j hj
    field_simp
  rw [he, gatedExcess_sum]
  by_cases hv : v = (fun _ => false)
  · subst v
    simp [nonemptyHit, hempty]
  · simp [nonemptyHit, hv]

#print axioms orderedHitValue_prefixAvoid
#print axioms normalized_cover_is_order_mixture
end Erdos970.FiniteSelberg
