import Submission.IntegerDifferenceCapacity

/-! Forbidden-support counts for every fixed positive-difference capacity.
These are ordinary integer carriers, not square carriers. -/
namespace Erdos773.IntegerDifferenceCapacityGeneral
open Finset IntegerDifferenceCapacity
set_option maxHeartbeats 3000000

def obstructions (m g : ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 m).biUnion (fun D =>
    ((reps (Icc 1 m) D).powersetCard (g+1)).image support)).filter
      (fun e => e.card=2*(g+1))

lemma obstructions_card (m g : ℕ) : (obstructions m g).card ≤ m^(g+2) := by
  calc
    _ ≤ ((Icc 1 m).biUnion (fun D =>
        ((reps (Icc 1 m) D).powersetCard (g+1)).image support)).card := card_filter_le _ _
    _ ≤ ∑ D ∈ Icc 1 m, (((reps (Icc 1 m) D).powersetCard (g+1)).image support).card := card_biUnion_le
    _ ≤ ∑ _D ∈ Icc 1 m, m^(g+1) := by
      apply sum_le_sum
      intro D hD
      apply card_image_le.trans
      rw [card_powersetCard]
      apply (Nat.choose_le_pow _ _).trans
      apply Nat.pow_le_pow_left
      simpa using reps_card (Icc 1 m) D
    _ = _ := by simp [pow_succ, Nat.mul_comm]

lemma obstructions_size {m g : ℕ} {e : Finset ℕ} (he : e ∈ obstructions m g) :
    e.card=2*(g+1) := (mem_filter.mp he).2

lemma obstructions_subset {m g : ℕ} {e : Finset ℕ} (he : e ∈ obstructions m g) :
    e ⊆ Icc 1 m := by
  obtain ⟨D,hD,he⟩ := mem_biUnion.mp (mem_filter.mp he).1
  obtain ⟨E,hE,rfl⟩ := mem_image.mp he
  exact support_subset (mem_powersetCard.mp hE).1

lemma capacity_of_avoids {m g : ℕ} {B : Finset ℕ} (hB : B ⊆ Icc 1 m)
    (hAP : ThreeAPFree (B:Set ℕ)) (havoid : ∀ e ∈ obstructions m g, ¬e ⊆ B) :
    ∀ D, 0<D → (reps B D).card ≤ g := by
  intro D hD
  by_contra! hlarge
  obtain ⟨E,hE,hcard⟩ := exists_subset_card_eq (show g+1 ≤ (reps B D).card by omega)
  have hE' : E ⊆ reps (Icc 1 m) D := by
    intro ab hab
    obtain ⟨habB,habD⟩ := mem_filter.mp (hE hab)
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨hB (mem_product.mp habB).1,hB (mem_product.mp habB).2⟩,habD⟩
  have hDm : D ≤ m := by
    obtain ⟨ab,hab⟩ := card_pos.mp (show 0<E.card by omega)
    obtain ⟨hp,hq⟩ := mem_filter.mp (hE' hab)
    have hb := mem_Icc.mp (mem_product.mp hp).2
    omega
  apply havoid (support E) _ (support_subset hE)
  apply mem_filter.mpr
  refine ⟨mem_biUnion.mpr ⟨D,mem_Icc.mpr ⟨hD,hDm⟩,
    mem_image.mpr ⟨E,mem_powersetCard.mpr ⟨hE',hcard⟩,rfl⟩⟩,?_⟩
  rw [support_card hAP hE,hcard]

#print axioms obstructions_card
#print axioms capacity_of_avoids
end Erdos773.IntegerDifferenceCapacityGeneral
