import Submission.GreedyBatchState
import Submission.FiniteHypergraphRestriction
import Submission.RegularizationSharedLinks

/-! Deterministic structural caps for a conservative batch and its actual
carrier restriction. No independence of the tentative mark set is needed. -/
namespace Erdos773.GreedyBatchStructure
open Finset GreedyBatchState FourUniformRegularization
open FiniteHypergraphRestriction
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma pair_le (H : Finset (Finset α)) (R : Finset α) (x y : α) :
    pairDegree (next H R) x y≤pairDegree H x y := by
  have hs : (next H R).filter (fun f => x∈f ∧ y∈f)⊆
      (H.filter (fun e => x∈e ∧ y∈e)).image (fun e => e \ R) := by
    intro f hf
    obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨(mem_filter.mp he).1,
      (mem_sdiff.mp hx).1,(mem_sdiff.mp hy).1⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

lemma intersections {H : Finset (Finset α)} (R : Finset α) (K : ℕ)
    (hK : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤K) :
    ∀ e∈next H R, ∀ f∈next H R, e≠f → (e∩f).card≤K := by
  intro e he f hf hef
  obtain ⟨a,ha,rfl⟩ := mem_image.mp he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
  have hab : a≠b := fun h => hef (congrArg (fun s => s \ R) h)
  apply (card_le_card (show (a \ R)∩(b \ R)⊆a∩b from ?_)).trans
    (hK a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab)
  intro x hx
  exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp hx).1).1,(mem_sdiff.mp (mem_inter.mp hx).2).1⟩

/-- Shared links transport to the genuine carrier without increasing their
count. No deleted ambient vertex enters the density model. -/
lemma shared_restrict {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    RegularizationSharedLinks.count (restrict Q H) x y≤RegularizationSharedLinks.count H x.val y.val := by
  apply card_le_card_of_injOn (up Q)
  · intro A hA
    obtain ⟨hAc,hxA,hyA,hx,hy⟩ := RegularizationSharedLinks.mem_links.mp hA
    have hx' : x.val∉up Q A := by
      intro hx
      obtain ⟨z,hz,hzx⟩ := mem_map.mp hx
      have he : z=x := Subtype.ext hzx
      exact hxA (he ▸ hz)
    have hy' : y.val∉up Q A := by
      intro hy
      obtain ⟨z,hz,hzy⟩ := mem_map.mp hy
      have he : z=y := Subtype.ext hzy
      exact hyA (he ▸ hz)
    have he := (mem_restrict hH).mp hx
    have hf := (mem_restrict hH).mp hy
    simp only [up,map_insert,Function.Embedding.subtype_apply] at he hf
    exact RegularizationSharedLinks.mem_links.mpr ⟨by rwa [up_card],hx',hy',he,hf⟩
  · exact fun A hA B hB he => up_injective Q he

#print axioms pair_le
#print axioms intersections
#print axioms shared_restrict
end
end Erdos773.GreedyBatchStructure
