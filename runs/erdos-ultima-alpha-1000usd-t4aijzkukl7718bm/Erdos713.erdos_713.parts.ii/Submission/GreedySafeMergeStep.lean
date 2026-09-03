import FormalConjecturesUtil
import Submission.UniformPairCost

/-! A greedy safe merger retaining many individually safe candidates.
Interactions and repeated endpoints are both charged explicitly. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713GreedySafeMergeStep
open Erdos713VertexMerging Erdos713C8TwoMergers Erdos713MergeDegreePenalty
variable {V : Type*}
set_option maxHeartbeats 2000000

lemma exists_small_fiber {I : Type*} [DecidableEq I] (S : Finset I)
    (T : Finset (I × I)) (B : ℕ) (hS : B < S.card) (hT : T.card ≤ B^2) :
    ∃ p ∈ S, (T.filter (fun q => q.1=p)).card ≤ B := by
  by_contra hh
  push_neg at hh
  have hs := sum_le_sum (s := S) (fun p hp => show B+1 ≤ (T.filter (fun q => q.1=p)).card by
    have := hh p hp
    omega)
  rw [sum_const,Nat.nsmul_eq_mul,sum_card_fiberwise_eq_card_filter] at hs
  have hu := card_filter_le T (fun q => q.1 ∈ S)
  nlinarith only [hs,hu,hT,hS]

noncomputable def starPairs [Fintype V] (a b : V) : Finset (V × V) :=
  ({a,b} ×ˢ univ) ∪ (univ ×ˢ {a,b})

lemma mem_starPairs [Fintype V] (a b : V) (p : V × V) :
    p ∈ starPairs a b ↔ p.1=a ∨ p.1=b ∨ p.2=a ∨ p.2=b := by
  simp only [starPairs,mem_union,mem_product,mem_insert,mem_singleton,mem_univ,and_true,true_and]
  tauto

lemma card_starPairs_le [Fintype V] (a b : V) : (starPairs a b).card ≤ 4*Fintype.card V := by
  have hu := card_union_le ({a,b} ×ˢ (univ : Finset V)) ((univ : Finset V) ×ˢ {a,b})
  simp only [card_product,card_univ] at hu
  have hc := card_le_two (a := a) (b := b)
  have hm := Nat.mul_le_mul_right (Fintype.card V) hc
  dsimp only [starPairs]
  nlinarith only [hu,hm]

/-- Cardinality loss is bounded by the two endpoint stars and one interaction
fiber. The surviving pairs exclude both old roots and are genuinely safe in
the merged graph. -/
theorem step [Fintype V] (G : SimpleGraph V) (hFree : (cycleGraph 8).Free G)
    (S : Finset (V × V)) (hSafe : ∀ p ∈ S, SafePair (cycleGraph 8) G p.1 p.2)
    (B : ℕ) (hS : B < S.card) (hB : (genuineRoots G).card ≤ B^2) :
    ∃ a b : V, ∃ _hab : a ≠ b, ∃ hn : ¬ G.Adj a b,
      (a,b) ∈ S ∧ (cycleGraph 8).Free (merge G a b hn) ∧
      ∃ T : Finset ({x : V // x ≠ b} × {x : V // x ≠ b}),
        S.card ≤ T.card+4*Fintype.card V+B ∧
        (∀ p ∈ T, (p.1.val,p.2.val) ∈ S ∧ p.1.val ≠ a ∧ p.2.val ≠ a) ∧
        ∀ p ∈ T, SafePair (cycleGraph 8) (merge G a b hn) p.1 p.2 := by
  obtain ⟨p,hp,hpB⟩ := exists_small_fiber S (genuineRoots G) B hS hB
  obtain ⟨hab,hn,hfirst⟩ := hSafe p hp
  let U := (genuineRoots G).filter (fun q => q.1=p)
  let E := U.image Prod.snd
  let R := S \ (starPairs p.1 p.2 ∪ E)
  have hE : E.card ≤ B := (card_image_le (s := U) (f := Prod.snd)).trans hpB
  have hR (q : R) : q.val ∈ S ∧ q.val.1 ≠ p.1 ∧ q.val.1 ≠ p.2 ∧
      q.val.2 ≠ p.1 ∧ q.val.2 ≠ p.2 ∧ ¬ GenuineDouble G p.1 p.2 q.val.1 q.val.2 := by
    have hs := (mem_sdiff.mp q.property).1
    have hnU := (mem_sdiff.mp q.property).2
    have hnStar : q.val ∉ starPairs p.1 p.2 := fun h => hnU (mem_union_left E h)
    have hnEq : q.val.1 ≠ p.1 ∧ q.val.1 ≠ p.2 ∧ q.val.2 ≠ p.1 ∧ q.val.2 ≠ p.2 := by
      simpa only [mem_starPairs,not_or] using hnStar
    refine ⟨hs,hnEq.1,hnEq.2.1,hnEq.2.2.1,hnEq.2.2.2,?_⟩
    intro hg
    apply hnU
    apply mem_union_right
    apply mem_image.mpr
    refine ⟨(p,q.val),?_,rfl⟩
    apply mem_filter.mpr
    exact ⟨mem_filter.mpr ⟨mem_univ _,hg⟩,rfl⟩
  let f : R → {x : V // x ≠ p.2} × {x : V // x ≠ p.2} := fun q =>
    (⟨q.val.1,(hR q).2.2.1⟩,⟨q.val.2,(hR q).2.2.2.2.1⟩)
  have hf : Function.Injective f := by
    intro q r he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z => z.1.val) he) (congrArg (fun z => z.2.val) he)
  let T := (univ : Finset R).image f
  have hT : T.card=R.card := by simp only [T,card_image_of_injective _ hf,card_univ,Fintype.card_coe]
  have hcount : S.card ≤ T.card+4*Fintype.card V+B := by
    have hsub : S ⊆ R ∪ (starPairs p.1 p.2 ∪ E) := by
      intro q hq
      by_cases he : q ∈ starPairs p.1 p.2 ∪ E
      · exact mem_union_right _ he
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hq,he⟩)
    have hc := card_le_card hsub
    have hu := card_union_le R (starPairs p.1 p.2 ∪ E)
    have hu' := card_union_le (starPairs p.1 p.2) E
    have hs := card_starPairs_le p.1 p.2
    omega
  refine ⟨p.1,p.2,hab,hn,hp,hfirst,T,hcount,?_,?_⟩
  · intro q hq
    obtain ⟨r,_,rfl⟩ := mem_image.mp hq
    exact ⟨(hR r).1,(hR r).2.1,(hR r).2.2.2.1⟩
  · intro q hq
    obtain ⟨r,_,rfl⟩ := mem_image.mp hq
    obtain ⟨hrS,hca,hcb,hda,hdb,hNot⟩ := hR r
    obtain ⟨hcd,hncd,hsecond⟩ := hSafe r.val hrS
    have hncd' : ¬ (merge G p.1 p.2 hn).Adj (f r).1 (f r).2 := by
      rw [merge_adj]
      simpa only [f,hca,hda,false_and,or_false] using hncd
    refine ⟨fun he => hcd (congrArg Subtype.val he),hncd',?_⟩
    intro hContains
    exact hNot ⟨hFree,hab,hca,hcb,hda,hdb,hcd,hn,hncd,hncd',hfirst,hsecond,hContains⟩

#print axioms exists_small_fiber
#print axioms step
end Erdos713GreedySafeMergeStep
