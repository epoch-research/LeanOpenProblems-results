import Submission.GreedyMixedCommonTails
import Submission.RegularizationSharedLinks

/-! Counting the one-selected-vertex common-neighbor witnesses of a mixed
hypergraph. The shared rank-three link count is explicit, not silently
bounded by the initial graph common degree. -/
namespace Erdos773.GreedyMixedCommonProfiles
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyMixedCommonTails
open HypergraphDegreeTrim FourUniformRegularization UniformLayerRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Patterns whose first edge has rank two. -/
def firstTwo (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (patterns H u v).filter (fun x => x.1.card=2)

def secondTwo (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (patterns H u v).filter (fun x => x.2.2.card=2)

lemma firstTwo_card (H : Finset (Finset α)) (u v : α) (P : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) :
    (firstTwo H u v).card≤degree (layer H 2) u*P := by
  let E := (layer H 2).filter (fun e => u∈e)
  have hs : firstTwo H u v ⊆ extensions H E v (fun e => e \ {u,v}) := by
    rintro ⟨e,w,f⟩ hx
    obtain ⟨hx,hcard⟩ := mem_filter.mp hx
    obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hx
    exact mem_extensions.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨he,hcard⟩,hu⟩,
      mem_sdiff.mpr ⟨hw,by simp [hwu,hwv]⟩,hf,hv,hwf⟩
  have hsize (e : Finset α) (he : e∈E) : (e \ {u,v}).card≤1 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    have hcard := (mem_filter.mp he).2
    have hsub : e \ {u,v}⊆e.erase u := by
      intro a ha
      exact mem_erase.mpr ⟨fun h => (mem_sdiff.mp ha).2 (by simp [h]),(mem_sdiff.mp ha).1⟩
    have hh := card_le_card hsub
    rw [card_erase_of_mem hu,hcard] at hh
    exact hh
  have hne (e : Finset α) (_he : e∈E) (w : α) (hw : w∈e \ {u,v}) : v≠w := by
    intro hvw
    exact (mem_sdiff.mp hw).2 (by simp [hvw])
  have hb := (card_le_card hs).trans (extensions_card_le H E v _ 1 P hsize hne hP)
  simpa only [Nat.mul_one] using hb

lemma secondTwo_card (H : Finset (Finset α)) (u v : α) (P : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P) :
    (secondTwo H u v).card≤degree (layer H 2) v*P := by
  apply (show (secondTwo H u v).card≤(firstTwo H v u).card from ?_).trans (firstTwo_card H v u P hP)
  apply card_le_card_of_injOn (fun x : Pattern α => (x.2.2,x.2.1,x.1))
  · rintro ⟨e,w,f⟩ hx
    obtain ⟨hx,hcard⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨pattern_swap hx,hcard⟩
  · rintro ⟨e,w,f⟩ _ ⟨e',w',f'⟩ _ he
    simpa only [Prod.mk.injEq,and_comm,and_left_comm,and_assoc] using he

/-- Each shared two-link supplies exactly two possible middle-vertex roles. -/
def twinPatterns (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (RegularizationSharedLinks.links H u v).biUnion
    (fun A => A.image (fun w => (insert u A,w,insert v A)))

lemma twinPatterns_card (H : Finset (Finset α)) (u v : α) :
    (twinPatterns H u v).card≤2*RegularizationSharedLinks.count H u v := by
  calc
    _ ≤ ∑ A∈RegularizationSharedLinks.links H u v,
      (A.image (fun w => (insert u A,w,insert v A))).card := card_biUnion_le
    _ ≤ ∑ A∈RegularizationSharedLinks.links H u v, A.card :=
      sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by
      rw [sum_congr rfl (fun A hA => (RegularizationSharedLinks.mem_links.mp hA).1)]
      simp [RegularizationSharedLinks.count,mul_comm]

lemma one_support_twin {H : Finset (Finset α)} {u v w : α} {e f : Finset α}
    (hx : (e,w,f)∈patterns H u v) (h1 : (witness u v (e,w,f)).card=1)
    (he2 : e.card≠2) (hf2 : f.card≠2) : (e,w,f)∈twinPatterns H u v := by
  obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,hve,huf⟩ := mem_patterns.mp hx
  obtain ⟨a,ha⟩ := card_eq_one.mp h1
  change (e \ {u,w})∪(f \ {v,w})={a} at ha
  have hepair : ({u,w} : Finset α)⊆e := by simp [insert_subset_iff,hu,hw]
  have hfpair : ({v,w} : Finset α)⊆f := by simp [insert_subset_iff,hv,hwf]
  have hene : (e \ {u,w}).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hsub
    have heq := Subset.antisymm hsub hepair
    apply he2
    rw [heq,card_pair hwu.symm]
  have hfne : (f \ {v,w}).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hsub
    have heq := Subset.antisymm hsub hfpair
    apply hf2
    rw [heq,card_pair hwv.symm]
  have heone : e \ {u,w}={a} := by
    have hs : e \ {u,w}⊆({a}:Finset α) := ha ▸ subset_union_left
    exact eq_singleton_iff_nonempty_unique_mem.mpr ⟨hene,fun b hb => mem_singleton.mp (hs hb)⟩
  have hfone : f \ {v,w}={a} := by
    have hs : f \ {v,w}⊆({a}:Finset α) := ha ▸ subset_union_right
    exact eq_singleton_iff_nonempty_unique_mem.mpr ⟨hfne,fun b hb => mem_singleton.mp (hs hb)⟩
  have hae : a∈e \ {u,w} := by rw [heone]; simp
  have haf : a∈f \ {v,w} := by rw [hfone]; simp
  have hau : a≠u := fun h => (mem_sdiff.mp hae).2 (by simp [h])
  have hav : a≠v := fun h => (mem_sdiff.mp haf).2 (by simp [h])
  have haw : a≠w := fun h => (mem_sdiff.mp hae).2 (by simp [h])
  have heq : e=insert u ({w,a}:Finset α) := by
    have hh := sdiff_union_of_subset hepair
    rw [heone] at hh
    simpa only [union_insert,union_singleton,insert_comm,insert_eq_of_mem (mem_singleton_self a)] using hh.symm
  have hfq : f=insert v ({w,a}:Finset α) := by
    have hh := sdiff_union_of_subset hfpair
    rw [hfone] at hh
    simpa only [union_insert,union_singleton,insert_comm,insert_eq_of_mem (mem_singleton_self a)] using hh.symm
  refine mem_biUnion.mpr ⟨{w,a},RegularizationSharedLinks.mem_links.mpr ⟨?_,?_,?_,?_,?_⟩,
    mem_image.mpr ⟨w,by simp,?_⟩⟩
  · exact card_pair haw.symm
  · simp [hwu.symm,hau.symm]
  · simp [hwv.symm,hav.symm]
  · rwa [← heq]
  · rwa [← hfq]
  · rw [← heq,← hfq]

/-- Every one-support pattern is a short-edge pattern or a shared
rank-three link. In particular, the latter cannot be charged at p^3. -/
lemma one_support_cover (H : Finset (Finset α)) (u v : α) :
    supportLayer H u v 1⊆(firstTwo H u v∪secondTwo H u v)∪twinPatterns H u v := by
  rintro ⟨e,w,f⟩ hx
  obtain ⟨hx,hcard⟩ := mem_filter.mp hx
  by_cases he : e.card=2
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx,he⟩))
  by_cases hf : f.card=2
  · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx,hf⟩))
  exact mem_union_right _ (one_support_twin hx hcard he hf)

/-- Explicit one-support budget. This theorem needs neither regularity nor
an intersection cap, and retains the necessary shared-link term. -/
theorem one_support_bound (H : Finset (Finset α)) (u v : α) (P B D : ℕ)
    (hP : ∀ a b, a≠b → pairDegree H a b≤P)
    (hu : degree (layer H 2) u≤D) (hv : degree (layer H 2) v≤D)
    (hB : RegularizationSharedLinks.count H u v≤B) :
    (supportLayer H u v 1).card≤2*D*P+2*B := by
  have h0 := card_le_card (one_support_cover H u v)
  have h1 := card_union_le (firstTwo H u v∪secondTwo H u v) (twinPatterns H u v)
  have h2 := card_union_le (firstTwo H u v) (secondTwo H u v)
  have h3 := (firstTwo_card H u v P hP).trans (Nat.mul_le_mul_right P hu)
  have h4 := (secondTwo_card H u v P hP).trans (Nat.mul_le_mul_right P hv)
  have h5 := (twinPatterns_card H u v).trans (Nat.mul_le_mul_left 2 hB)
  simp only [Nat.mul_assoc]
  omega

#print axioms firstTwo_card
#print axioms twinPatterns_card
#print axioms one_support_twin
#print axioms one_support_bound
end
end Erdos773.GreedyMixedCommonProfiles
