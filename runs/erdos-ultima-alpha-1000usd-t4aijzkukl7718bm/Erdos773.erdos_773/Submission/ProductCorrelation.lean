import FormalConjecturesUtil

/-!
Finite product distributions on chains and positive correlation of increasing
functions. These are probability/averaging lemmas, not a Sidon construction.
-/
namespace Erdos773.ProductCorrelation
open Finset
set_option maxHeartbeats 1000000

section Lattice
variable {Ω ι : Type*} [Fintype Ω] [DistribLattice Ω] [DecidableEq ι]

/-- The normalized FKG inequality, for a log-supermodular finite mass. -/
lemma correlated (μ f g : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfn : Monotone f) (hgn : Monotone g)
    (hmod : ∀ x y, μ x * μ y ≤ μ (x ⊓ y) * μ (x ⊔ y))
    (hsum : ∑ x, μ x = 1) :
    (∑ x, μ x * f x) * (∑ x, μ x * g x) ≤ ∑ x, μ x * (f x * g x) := by
  simpa only [hsum, one_mul] using fkg f g μ hμ hf hg hfn hgn hmod

/-- Positive correlation for any finite family of nonnegative increasing
functions. No disjointness between their coordinate supports is needed. -/
lemma product_correlated (μ : Ω → ℝ) (F : ι → Ω → ℝ) (s : Finset ι)
    (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1)
    (hmod : ∀ x y, μ x * μ y ≤ μ (x ⊓ y) * μ (x ⊔ y))
    (hF : ∀ i ∈ s, ∀ x, 0 ≤ F i x) (hmono : ∀ i ∈ s, Monotone (F i)) :
    (∏ i ∈ s, ∑ x, μ x * F i x) ≤ ∑ x, μ x * ∏ i ∈ s, F i x := by
  induction s using Finset.induction_on with
  | empty => simp [hsum]
  | @insert i s hi ih =>
    have hiF := hF i (mem_insert_self i s)
    have hsF : ∀ j ∈ s, ∀ x, 0 ≤ F j x := fun j hj => hF j (mem_insert_of_mem hj)
    have hsmono : ∀ j ∈ s, Monotone (F j) := fun j hj => hmono j (mem_insert_of_mem hj)
    have hpF : ∀ x, 0 ≤ ∏ j ∈ s, F j x := fun x => prod_nonneg (fun j hj => hsF j hj x)
    have hpmono : Monotone (fun x => ∏ j ∈ s, F j x) := by
      intro x y hxy
      exact prod_le_prod (fun j hj => hsF j hj x) (fun j hj => hsmono j hj hxy)
    simp only [prod_insert hi]
    calc
      _ ≤ (∑ x, μ x * F i x) * ∑ x, μ x * ∏ j ∈ s, F j x :=
        mul_le_mul_of_nonneg_left (ih hsF hsmono) (sum_nonneg (fun x _ => mul_nonneg (hμ x) (hiF x)))
      _ ≤ _ := correlated μ (F i) (fun x => ∏ j ∈ s, F j x) hμ hiF hpF
        (hmono i (mem_insert_self i s)) hpmono hmod hsum
end Lattice

section Product
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

noncomputable def weight (W : α → β → ℝ) (x : α → β) : ℝ := ∏ i, W i (x i)

omit [DecidableEq α] [Fintype β] in
lemma weight_nonneg (W : α → β → ℝ) (hW : ∀ i t, 0 ≤ W i t) (x : α → β) :
    0 ≤ weight W x := prod_nonneg (fun i _ => hW i (x i))

lemma sum_weight (W : α → β → ℝ) (hW : ∀ i, ∑ t, W i t = 1) :
    ∑ x, weight W x = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp_rw [hW]
  simp

lemma sum_weight_restrict (W : α → β → ℝ) (P : α → β → Prop)
    [∀ i t, Decidable (P i t)] :
    (∑ x, if ∀ i, P i (x i) then weight W x else 0) =
      ∏ i, ∑ t, if P i t then W i t else 0 := by
  have he (x : α → β) :
      (if ∀ i, P i (x i) then weight W x else 0) =
        ∏ i, if P i (x i) then W i (x i) else 0 := by
    by_cases h : ∀ i, P i (x i)
    · simp [h, weight]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      symm
      apply prod_eq_zero (mem_univ i)
      simp [hi]
  simp_rw [he]
  exact (Fintype.prod_sum (fun i t => if P i t then W i t else 0)).symm

omit [DecidableEq α] [Fintype β] in
/-- Product masses on finite chains are log-modular, even when some masses
vanish. This includes point-mass conditioning on one coordinate. -/
lemma weight_modular [LinearOrder β] (W : α → β → ℝ) (x y : α → β) :
    weight W x * weight W y = weight W (x ⊓ y) * weight W (x ⊔ y) := by
  simp only [weight, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  change W i (x i) * W i (y i) = W i (min (x i) (y i)) * W i (max (x i) (y i))
  rcases le_total (x i) (y i) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

lemma weight_product_correlated [LinearOrder β] {ι : Type*} [DecidableEq ι]
    (W : α → β → ℝ) (F : ι → (α → β) → ℝ) (s : Finset ι)
    (hW : ∀ i t, 0 ≤ W i t) (hsum : ∀ i, ∑ t, W i t = 1)
    (hF : ∀ i ∈ s, ∀ x, 0 ≤ F i x) (hmono : ∀ i ∈ s, Monotone (F i)) :
    (∏ i ∈ s, ∑ x, weight W x * F i x) ≤
      ∑ x, weight W x * ∏ i ∈ s, F i x :=
  product_correlated (weight W) F s (weight_nonneg W hW) (sum_weight W hsum)
    (fun x y => (weight_modular W x y).le) hF hmono

variable [DecidableEq β]

/-- Fix one coordinate, leaving all other marginal distributions unchanged. -/
def pin (W : α → β → ℝ) (v : α) (t : β) (i : α) (s : β) : ℝ :=
  if i = v then (if s = t then 1 else 0) else W i s

omit [Fintype α] [Fintype β] in
lemma pin_nonneg (W : α → β → ℝ) (hW : ∀ i t, 0 ≤ W i t) (v : α) (t : β) :
    ∀ i s, 0 ≤ pin W v t i s := by
  intro i s
  dsimp [pin]
  split_ifs <;> first | positivity | exact hW i s

omit [Fintype α] in
lemma pin_sum (W : α → β → ℝ) (hW : ∀ i, ∑ t, W i t = 1) (v : α) (t : β) :
    ∀ i, ∑ s, pin W v t i s = 1 := by
  intro i
  by_cases h : i = v
  · simp [pin, h]
  · simpa [pin, h] using hW i

omit [Fintype β] in
lemma weight_pin (W : α → β → ℝ) (v : α) (t : β) (x : α → β) :
    weight (pin W v t) x =
      if x v = t then ∏ i ∈ univ.erase v, W i (x i) else 0 := by
  unfold weight
  rw [← mul_prod_erase univ (fun i => pin W v t i (x i)) (mem_univ v)]
  have he : (∏ i ∈ univ.erase v, pin W v t i (x i)) =
      ∏ i ∈ univ.erase v, W i (x i) := by
    apply prod_congr rfl
    intro i hi
    simp only [pin, if_neg (mem_erase.mp hi).1]
  rw [he]
  simp [pin]

lemma weight_mixture (W : α → β → ℝ) (v : α) (x : α → β) :
    (∑ t, W v t * weight (pin W v t) x) = weight W x := by
  simp_rw [weight_pin, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]
  exact mul_prod_erase univ (fun i => W i (x i)) (mem_univ v)

lemma expectation_mixture (W : α → β → ℝ) (v : α) (f : (α → β) → ℝ) :
    (∑ x, weight W x * f x) =
      ∑ t, W v t * ∑ x, weight (pin W v t) x * f x := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← weight_mixture W v x, sum_mul]
  apply sum_congr rfl
  intro t _
  ring

end Product
#print axioms product_correlated
#print axioms sum_weight_restrict
#print axioms weight_product_correlated
end Erdos773.ProductCorrelation
