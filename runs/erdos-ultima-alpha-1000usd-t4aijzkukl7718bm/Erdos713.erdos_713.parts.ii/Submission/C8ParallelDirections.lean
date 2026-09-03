import FormalConjecturesUtil
import Submission.C8CommutingGeneratorSets
import Submission.C8FiberDifferences

/-! A bounded number of commuting parallel classes bounds the full difference
set of a C8-free Cayley graph. Auxiliary construction diagnostic only. -/
open SimpleGraph Finset
namespace Erdos713C8ParallelDirections
open Erdos713C8CommutingDifferences Erdos713C8CommutingGeneratorSets
open Erdos713C8FiberDifferences (differences)
variable {G I D T : Type*} [Group G] [Fintype I]
set_option maxHeartbeats 2000000

def ParallelCommute (τ : D → I → T) (g : I → G) : Prop :=
  ∀ m a b c d, τ m a = τ m b → τ m c = τ m d →
    Commute (g a*(g b)⁻¹) (g c*(g d)⁻¹)

open scoped Classical in
noncomputable def directionDifferences (τ : D → I → T) (g : I → G) (m : D) : Finset G :=
  (univ.filter (fun p : I × I => τ m p.1 = τ m p.2)).image
    (fun p => g p.1*(g p.2)⁻¹)

lemma direction_card (τ : D → I → T) (g : I → G) (hg : Function.Injective g)
    (hf : (cycleGraph 8).Free (graph g)) (hc : ParallelCommute τ g) (m : D) :
    (directionDifferences τ g m).card ≤ 25 := by
  classical
  by_cases hh : ∃ a b, a ≠ b ∧ τ m a = τ m b
  · obtain ⟨a,b,hab,habτ⟩ := hh
    let S := univ.filter (fun i => τ m i = τ m a)
    have ha : a ∈ S := by simp [S]
    have hb : b ∈ S := by simp [S,habτ.symm]
    have hS : S.card ≤ 5 := by
      apply card_le_five g hg hf S
      intro x hx y hy z hz w hw
      exact hc m x y z w
        (((mem_filter.mp hx).2).trans ((mem_filter.mp hy).2).symm)
        (((mem_filter.mp hz).2).trans ((mem_filter.mp hw).2).symm)
    have hsub : directionDifferences τ g m ⊆
        (S ×ˢ S).image (fun p => g p.1*(g p.2)⁻¹) := by
      intro x hx
      obtain ⟨⟨c,d⟩,hcdτ,rfl⟩ := mem_image.mp hx
      have hτ : τ m c = τ m d := (mem_filter.mp hcdτ).2
      by_cases hcS : c ∈ S
      · have hdS : d ∈ S := mem_filter.mpr ⟨mem_univ _,
          hτ.symm.trans (mem_filter.mp hcS).2⟩
        exact mem_image.mpr ⟨(c,d),mem_product.mpr ⟨hcS,hdS⟩,rfl⟩
      have hdS : d ∉ S := by
        intro hd
        exact hcS (mem_filter.mpr ⟨mem_univ _,hτ.trans (mem_filter.mp hd).2⟩)
      by_cases hcd : c = d
      · subst d
        exact mem_image.mpr ⟨(a,a),mem_product.mpr ⟨ha,ha⟩,by simp⟩
      have hca : a ≠ c := by rintro rfl; exact hcS ha
      have hcb : b ≠ c := by rintro rfl; exact hcS hb
      have hda : a ≠ d := by rintro rfl; exact hdS ha
      have hdb : b ≠ d := by rintro rfl; exact hdS hb
      have h := Erdos713C8CommutingGeneratorSets.difference_dichotomy g hg hf
        a b c d hab hca hda hcb hdb hcd (hc m a b c d habτ hτ)
      rcases h with h | h
      · exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,h.symm⟩
      · refine mem_image.mpr ⟨(b,a),mem_product.mpr ⟨hb,ha⟩,?_⟩
        simpa only [mul_inv_rev,inv_inv] using h.symm
    calc
      _ ≤ ((S ×ˢ S).image (fun p => g p.1*(g p.2)⁻¹)).card := card_le_card hsub
      _ ≤ (S ×ˢ S).card := card_image_le
      _ = S.card*S.card := card_product _ _
      _ ≤ 5*5 := Nat.mul_le_mul hS hS
  · have hsub : directionDifferences τ g m ⊆ {1} := by
      intro x hx
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hx
      have he : a = b := by
        by_contra hn
        exact hh ⟨a,b,hn,(mem_filter.mp hab).2⟩
      simp [he]
    have hle := card_le_card hsub
    simp only [card_singleton] at hle
    omega

/-- Every pair is assigned at least one direction; uniqueness is unnecessary.
All parallel classes in a direction have commuting differences with each other. -/
theorem differences_card [Fintype D] (τ : D → I → T) (g : I → G)
    (hg : Function.Injective g) (hf : (cycleGraph 8).Free (graph g))
    (hc : ParallelCommute τ g) (hcover : ∀ a b, ∃ m, τ m a = τ m b) :
    (differences g).card ≤ 25*Fintype.card D := by
  classical
  have hsub : differences g ⊆ univ.biUnion (directionDifferences τ g) := by
    intro x hx
    obtain ⟨⟨a,b⟩,_,rfl⟩ := mem_image.mp hx
    obtain ⟨m,hm⟩ := hcover a b
    exact mem_biUnion.mpr ⟨m,mem_univ _,mem_image.mpr
      ⟨(a,b),mem_filter.mpr ⟨mem_univ _,hm⟩,rfl⟩⟩
  calc
    _ ≤ (univ.biUnion (directionDifferences τ g)).card := card_le_card hsub
    _ ≤ ∑ m : D, (directionDifferences τ g m).card := card_biUnion_le
    _ ≤ ∑ _m : D, 25 := sum_le_sum (fun m _ => direction_card τ g hg hf hc m)
    _ = _ := by simp [Nat.mul_comm]

#print axioms direction_card
#print axioms differences_card
end Erdos713C8ParallelDirections
