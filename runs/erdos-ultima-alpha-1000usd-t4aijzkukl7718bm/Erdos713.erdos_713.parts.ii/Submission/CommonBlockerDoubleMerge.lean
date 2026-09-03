import FormalConjecturesUtil
import Submission.DoubleMergeCost
import Submission.VertexRobustSplit
import Submission.C8TwoMergers

/-! A common vertex blocker is charged against a two-merger decrement.
This is a finite weighted comparison; the existence of cheap common
blockers, or a degree cap on exact extremizers, is not asserted. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713CommonBlockerDoubleMerge
open Erdos713VertexMerging Erdos713DoubleMergeCost Erdos713VertexRobustSplit
open Erdos713UniformIncidence Erdos713C8TwoMergers Erdos713TwoPathRootCounting
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma safe_delete_double_merge_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (S : Finset V) (a b c d : ↥((S : Set V)ᶜ))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hcd : c ≠ d) (hn : ¬ (G.induce (S : Set V)ᶜ).Adj a b)
    (hncd : ¬ (merge (G.induce (S : Set V)ᶜ) a b hn).Adj ⟨c,hcb⟩ ⟨d,hdb⟩)
    (hf : H.Free (merge (merge (G.induce (S : Set V)ᶜ) a b hn) ⟨c,hcb⟩ ⟨d,hdb⟩ hncd)) :
    extremalNumber (Fintype.card V) H ≤
      extremalNumber (Fintype.card V-S.card-2) H+
      (∑ z ∈ S, Nat.card (G.neighborSet z))+
      Nat.card (G.commonNeighbors a.val b.val)+Nat.card (G.commonNeighbors c.val d.val)+1 := by
  have hne : (⟨c,hcb⟩ : {x : ↥((S : Set V)ᶜ) // x ≠ b}) ≠ ⟨d,hdb⟩ :=
    fun hh => hcd (congrArg Subtype.val hh)
  have hb := safe_double_merge_bound H (G.induce (S : Set V)ᶜ) hab hn
    ⟨c,hcb⟩ ⟨d,hdb⟩ hca hda hne hncd hf
  have habC := common_induce_le G (S : Set V)ᶜ a b
  have hcdC := common_induce_le G (S : Set V)ᶜ c d
  have hdel := edges_le_induce_compl_add_degree G S
  have hcard : Fintype.card ↥((S : Set V)ᶜ) = Fintype.card V-S.card := by
    change Fintype.card {x : V // x ∉ S} = _
    rw [Fintype.card_subtype_compl]
    simp
  dsimp only at hb
  rw [hcard] at hb
  omega

lemma double_contains_of_delete_cost [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (S : Finset V) (a b c d : ↥((S : Set V)ᶜ))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hcd : c ≠ d) (hn : ¬ (G.induce (S : Set V)ᶜ).Adj a b)
    (hncd : ¬ (merge (G.induce (S : Set V)ᶜ) a b hn).Adj ⟨c,hcb⟩ ⟨d,hdb⟩)
    (hcost : ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ)+
      (Nat.card (G.commonNeighbors a.val b.val) : ℝ)+
      (Nat.card (G.commonNeighbors c.val d.val) : ℝ)+1 <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-S.card-2) H : ℝ)) :
    H ⊑ merge (merge (G.induce (S : Set V)ᶜ) a b hn) ⟨c,hcb⟩ ⟨d,hdb⟩ hncd := by
  by_contra hh
  have hb := safe_delete_double_merge_bound H G he S a b c d hab hca hcb hda hdb hcd hn hncd hh
  have hbR : (extremalNumber (Fintype.card V) H : ℝ) ≤
      (extremalNumber (Fintype.card V-S.card-2) H : ℝ)+
      ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ)+
      (Nat.card (G.commonNeighbors a.val b.val) : ℝ)+
      (Nat.card (G.commonNeighbors c.val d.val) : ℝ)+1 := by exact_mod_cast hb
  linarith

/-- If deletion makes each merger safe but costs less than the two-merger
backward decrement, their quadruple belongs to the previously counted
set of eight-edge two-walk configurations in the retained graph. -/
theorem c8_common_blocker_mem_total [Fintype V] (G : SimpleGraph V)
    (hf : (cycleGraph 8).Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) (cycleGraph 8))
    (S : Finset V) (a b c d : ↥((S : Set V)ᶜ))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hcd : c ≠ d) (hn : ¬ (G.induce (S : Set V)ᶜ).Adj a b)
    (hncd : ¬ (G.induce (S : Set V)ᶜ).Adj c d)
    (hfirst : (cycleGraph 8).Free (merge (G.induce (S : Set V)ᶜ) a b hn))
    (hsecond : (cycleGraph 8).Free (merge (G.induce (S : Set V)ᶜ) c d hncd))
    (hcost : ((∑ z ∈ S, Nat.card (G.neighborSet z)) : ℝ)+
      (Nat.card (G.commonNeighbors a.val b.val) : ℝ)+
      (Nat.card (G.commonNeighbors c.val d.val) : ℝ)+1 <
      (extremalNumber (Fintype.card V) (cycleGraph 8) : ℝ)-
        (extremalNumber (Fintype.card V-S.card-2) (cycleGraph 8) : ℝ)) :
    ((a,b),(c,d)) ∈ totalLengthRoots (G.induce (S : Set V)ᶜ) 8 := by
  have hncd' : ¬ (merge (G.induce (S : Set V)ᶜ) a b hn).Adj ⟨c,hcb⟩ ⟨d,hdb⟩ := by
    rw [merge_adj]
    simpa only [hca,hda,false_and,or_false] using hncd
  apply genuine_mem_total
  exact ⟨(fun hh => hf (hh.trans ⟨Copy.induce G _⟩)),hab,hca,hcb,hda,hdb,hcd,hn,hncd,
    hncd',hfirst,hsecond,
    double_contains_of_delete_cost (cycleGraph 8) G he S a b c d hab hca hcb hda hdb hcd hn hncd' hcost⟩

#print axioms safe_delete_double_merge_bound
#print axioms c8_common_blocker_mem_total
end Erdos713CommonBlockerDoubleMerge
