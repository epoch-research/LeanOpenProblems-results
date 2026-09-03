import Submission.ProductMomentObstruction
import Submission.SieveCertificateTransfer

/-! A Boolean block model deletes the all-unhit atom but preserves every
intersection moment whose degree is smaller than the number of blocks.
This is a synthetic moment model, not an interval cover. -/
namespace Erdos970.BlockMomentObstruction
open Finset
open Erdos970.FiniteSelberg
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {ι : β → Type*} [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]

abbrev Pattern := (j : β) → ι j → Bool
abbrev Support := (j : β) → Finset (ι j)

def degree (T : Support (ι := ι)) : ℕ := ∑ j, (T j).card

noncomputable def test (T : Support (ι := ι)) (v : Pattern (ι := ι)) : ℝ :=
  ∏ j, hitMonomial (T j) (v j)

noncomputable def model (q : (j : β) → ι j → ℝ) (v : Pattern (ι := ι)) : ℝ :=
  ProductMomentObstruction.weight (fun j => probability (q j)) (fun _ _ => false) v

lemma probability_nonneg (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1) (j : β) (v : ι j → Bool) :
    0 ≤ probability (q j) v := by
  apply prod_nonneg
  intro i hi
  cases v i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr (hq j i).2
  · exact (hq j i).1

lemma probability_sum (q : (j : β) → ι j → ℝ) (j : β) :
    (∑ v, probability (q j) v) = 1 := by
  simpa [average] using average_one (q j)

lemma probability_empty (q : (j : β) → ι j → ℝ) (j : β) :
    probability (q j) (fun _ => false) = ∏ i, (1 - q j i) := by simp [probability]

lemma model_nonneg (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2) (v : Pattern (ι := ι)) :
    0 ≤ model q v := by
  apply ProductMomentObstruction.weight_nonneg
  · exact probability_nonneg q hq
  · simpa only [probability_empty] using hhalf

lemma model_empty (q : (j : β) → ι j → ℝ) : model q (fun _ _ => false) = 0 :=
  ProductMomentObstruction.weight_at_distinguished _ _

lemma model_sum [Nonempty β] (q : (j : β) → ι j → ℝ)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2) : (∑ v, model q v) = 1 := by
  apply ProductMomentObstruction.weight_sum
  · exact probability_sum q
  · intro j
    rw [probability_empty]
    linarith [hhalf j]

lemma missing_block (T : Support (ι := ι)) (hdeg : degree T < Fintype.card β) :
    ∃ j, T j = ∅ := by
  by_contra hbad
  push_neg at hbad
  have hcard (j : β) : 1 ≤ (T j).card := card_pos.mpr (hbad j)
  have hh := sum_le_sum (s := univ) (fun j _ => hcard j)
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at hh
  unfold degree at hdeg
  omega

/-- All intersection moments below the block count are preserved EXACTLY. -/
theorem exact_moment (q : (j : β) → ι j → ℝ)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2)
    (T : Support (ι := ι)) (hdeg : degree T < Fintype.card β) :
    (∑ v, model q v * test T v) = ∏ j, ∏ i ∈ T j, q j i := by
  obtain ⟨j, hj⟩ := missing_block T hdeg
  have hh := ProductMomentObstruction.proper_product_moment
    (fun j => probability (q j)) (fun _ _ => false) (probability_sum q)
    (fun j => by dsimp only; rw [probability_empty]; linarith [hhalf j])
    (fun j => hitMonomial (T j)) j (fun v => by simp [hj, hitMonomial])
  change (∑ v, model q v * test T v) = ∏ j, average (q j) (hitMonomial (T j)) at hh
  simpa only [average_hitMonomial] using hh

/-- This includes arbitrary signed polynomial coefficients and imposes no
coefficient-cost restriction. It is stronger than a failure of one optimizer. -/
theorem no_positive_low_degree_polynomial {α : Type*} [Fintype α]
    (q : (j : β) → ι j → ℝ) (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2)
    (c : α → ℝ) (T : α → Support (ι := ι))
    (hdeg : ∀ t, degree (T t) < Fintype.card β)
    (hpoint : ∀ v : Pattern (ι := ι), v ≠ (fun _ _ => false) →
      (∑ t, c t * test (T t) v) ≤ 0) :
    (∑ t, c t * ∏ j, ∏ i ∈ T t j, q j i) ≤ 0 := by
  have hh := ProductMomentObstruction.no_positive_lower_polynomial
    (fun j => probability (q j)) (fun _ _ => false)
    (probability_nonneg q hq) (probability_sum q)
    (fun j => by simpa only [probability_empty] using hhalf j)
    c (fun t j => hitMonomial (T t j))
    (fun t => by obtain ⟨j, hj⟩ := missing_block (T t) (hdeg t)
                 exact ⟨j, fun v => by simp [hj, hitMonomial]⟩) hpoint
  change (∑ t, c t * ∏ j, average (q j) (hitMonomial (T t j))) ≤ 0 at hh
  simpa only [average_hitMonomial] using hh

/-- Multiplying by any mass preserves the exact low-order moments. The model
has no all-unhit atom and is nonnegative for a nonnegative mass. -/
theorem scaled_model [Nonempty β] (q : (j : β) → ι j → ℝ)
    (hq : ∀ j i, 0 ≤ q j i ∧ q j i ≤ 1)
    (hhalf : ∀ j, (∏ i, (1 - q j i)) ≤ 1 / 2) (X : ℝ) (hX : 0 ≤ X) :
    ∃ w : Pattern (ι := ι) → ℝ, (∀ v, 0 ≤ w v) ∧
      w (fun _ _ => false) = 0 ∧ (∑ v, w v) = X ∧
      ∀ T : Support (ι := ι), degree T < Fintype.card β →
        (∑ v, w v * test T v) = X * ∏ j, ∏ i ∈ T j, q j i := by
  refine ⟨fun v => X * model q v, (fun v => mul_nonneg hX (model_nonneg q hq hhalf v)),
    by simp [model_empty], ?_, ?_⟩
  · rw [← mul_sum, model_sum q hhalf, mul_one]
  · intro T hT
    simp_rw [mul_assoc]
    rw [← mul_sum, exact_moment q hhalf T hT]

#print axioms exact_moment
#print axioms no_positive_low_degree_polynomial
#print axioms scaled_model
end Erdos970.BlockMomentObstruction
