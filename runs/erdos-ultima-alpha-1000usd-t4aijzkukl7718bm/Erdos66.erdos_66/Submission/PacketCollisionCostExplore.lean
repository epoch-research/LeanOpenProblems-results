import Submission.MultiPacketSelectionExplore

/-! Collision costs for ordered coordinates, charged to the largest index
appearing in a point collision or a non-designated pair collision. -/
namespace Erdos66PacketCollisionCost
open Erdos66MultiPacketSelection
open scoped Classical
set_option maxHeartbeats 1000000

lemma weighted_fiber_bound {κ : Type*} {M : ℕ} (E : Finset κ) (v : κ → Fin M)
    (w C : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ i, ((E.filter (fun e ↦ v e = i)).card : ℝ) ≤ C i) :
    (∑ e ∈ E, w (v e)) ≤ ∑ i, C i * w i := by
  rw [← Finset.sum_fiberwise E v (fun e ↦ w (v e))]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = ∑ _e ∈ E.filter (fun e ↦ v e = i), w i := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = ((E.filter (fun e ↦ v e = i)).card : ℝ) * w i := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc i) (hw i)

noncomputable def prefixLabels {M : ℕ} (i : Fin M) : Finset (Label (Fin M)) :=
  (Finset.Iic i).product Finset.univ

lemma prefixLabels_card {M : ℕ} (i : Fin M) : (prefixLabels i).card = 2 * (i.val + 1) := by
  simp [prefixLabels, Finset.product_eq_sprod, Finset.card_product, Nat.mul_comm]

lemma mem_prefixLabels {M : ℕ} (i : Fin M) (u : Label (Fin M)) :
    u ∈ prefixLabels i ↔ u.1 ≤ i := by simp [prefixLabels]

def largest₂ {M : ℕ} (p : Label (Fin M) × Label (Fin M)) : Fin M := max p.1.1 p.2.1

def largest₄ {M : ℕ} (p : Quad (Fin M)) : Fin M :=
  max (max p.1.1 p.2.1.1) (max p.2.2.1.1 p.2.2.2.1)

lemma largest₂_mem {M : ℕ} (p : Label (Fin M) × Label (Fin M)) :
    largest₂ p = p.1.1 ∨ largest₂ p = p.2.1 := max_choice _ _

lemma largest₄_mem {M : ℕ} (p : Quad (Fin M)) :
    largest₄ p = p.1.1 ∨ largest₄ p = p.2.1.1 ∨
      largest₄ p = p.2.2.1.1 ∨ largest₄ p = p.2.2.2.1 := by
  rcases max_choice (max p.1.1 p.2.1.1) (max p.2.2.1.1 p.2.2.2.1) with h | h
  · rcases max_choice p.1.1 p.2.1.1 with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl (h.trans h'))
  · rcases max_choice p.2.2.1.1 p.2.2.2.1 with h' | h'
    · exact Or.inr (Or.inr (Or.inl (h.trans h')))
    · exact Or.inr (Or.inr (Or.inr (h.trans h')))

lemma point_fiber_card {M : ℕ} (i : Fin M) :
    (((pointEvents : Finset (Label (Fin M) × Label (Fin M))).filter
      (fun p ↦ largest₂ p = i)).card : ℝ) ≤ 4 * ((i.val : ℝ) + 1) ^ 2 := by
  have hsub : (pointEvents : Finset (Label (Fin M) × Label (Fin M))).filter
      (fun p ↦ largest₂ p = i) ⊆ (prefixLabels i).product (prefixLabels i) := by
    intro p hp
    have he := (Finset.mem_filter.mp hp).2
    have hu : p.1.1 ≤ i := he ▸ le_max_left _ _
    have hv : p.2.1 ≤ i := he ▸ le_max_right _ _
    exact Finset.mem_product.mpr ⟨(mem_prefixLabels i _).mpr hu, (mem_prefixLabels i _).mpr hv⟩
  have hh := Finset.card_le_card hsub
  simp only [Finset.product_eq_sprod, Finset.card_product, prefixLabels_card] at hh
  have hh' : (((pointEvents : Finset (Label (Fin M) × Label (Fin M))).filter
      (fun p ↦ largest₂ p = i)).card : ℝ) ≤ (2 * ((i.val : ℝ)+1)) * (2 * ((i.val : ℝ)+1)) := by
    exact_mod_cast hh
  nlinarith

lemma pair_fiber_card {M : ℕ} (i : Fin M) :
    (((pairEvents : Finset (Quad (Fin M))).filter (fun p ↦ largest₄ p = i)).card : ℝ) ≤
      16 * ((i.val : ℝ) + 1) ^ 4 := by
  let L := prefixLabels i
  have hsub : (pairEvents : Finset (Quad (Fin M))).filter (fun p ↦ largest₄ p = i) ⊆
      L.product (L.product (L.product L)) := by
    intro p hp
    have he := (Finset.mem_filter.mp hp).2
    have h₁ : p.1.1 ≤ i := he ▸ (le_max_left _ _).trans (le_max_left _ _)
    have h₂ : p.2.1.1 ≤ i := he ▸ (le_max_right _ _).trans (le_max_left _ _)
    have h₃ : p.2.2.1.1 ≤ i := he ▸ (le_max_left _ _).trans (le_max_right _ _)
    have h₄ : p.2.2.2.1 ≤ i := he ▸ (le_max_right _ _).trans (le_max_right _ _)
    exact Finset.mem_product.mpr ⟨(mem_prefixLabels i _).mpr h₁, Finset.mem_product.mpr
      ⟨(mem_prefixLabels i _).mpr h₂, Finset.mem_product.mpr
        ⟨(mem_prefixLabels i _).mpr h₃, (mem_prefixLabels i _).mpr h₄⟩⟩⟩
  have hh := Finset.card_le_card hsub
  simp only [Finset.product_eq_sprod, Finset.card_product, L, prefixLabels_card] at hh
  have hh' : (((pairEvents : Finset (Quad (Fin M))).filter (fun p ↦ largest₄ p = i)).card : ℝ) ≤
      (2 * ((i.val : ℝ)+1)) * ((2 * ((i.val : ℝ)+1)) *
        ((2 * ((i.val : ℝ)+1)) * (2 * ((i.val : ℝ)+1)))) := by exact_mod_cast hh
  nlinarith

/-- Bounds uniform in the number of selected coordinates, when the weighted
series on the right has a small tail. -/
theorem collision_cost_bounds {M : ℕ} (q : Fin M → ℕ) :
    (∑ p ∈ (pointEvents : Finset (Label (Fin M) × Label (Fin M))), 1 / (q (largest₂ p) : ℝ)) ≤
      ∑ i : Fin M, 4 * ((i.val : ℝ) + 1) ^ 2 / q i ∧
    (∑ p ∈ (pairEvents : Finset (Quad (Fin M))), 1 / (q (largest₄ p) : ℝ)) ≤
      ∑ i : Fin M, 16 * ((i.val : ℝ) + 1) ^ 4 / q i := by
  constructor
  · simpa only [mul_one_div] using weighted_fiber_bound pointEvents largest₂
      (fun i ↦ 1 / (q i : ℝ)) (fun i ↦ 4 * ((i.val : ℝ)+1)^2)
      (fun i ↦ by positivity) point_fiber_card
  · simpa only [mul_one_div] using weighted_fiber_bound pairEvents largest₄
      (fun i ↦ 1 / (q i : ℝ)) (fun i ↦ 16 * ((i.val : ℝ)+1)^4)
      (fun i ↦ by positivity) pair_fiber_card

end Erdos66PacketCollisionCost
