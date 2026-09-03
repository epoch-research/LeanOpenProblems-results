import FormalConjecturesUtil
import Submission.MergeBackward

/-! Identifying one pair can increase the overlap of a disjoint pair by
at most one. Consequently two nonadjacent identifications lose at most
the two original overlaps plus one edge. -/
open SimpleGraph
namespace Erdos713DoubleMergeCost
open Erdos713VertexMerging Erdos713MergeBackward
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma common_after_merge_le [Fintype V] (G : SimpleGraph V) (a b : V)
    (hn : ¬ G.Adj a b) (c d : {x : V // x ≠ b})
    (hca : c.val ≠ a) (hda : d.val ≠ a) :
    Nat.card ((merge G a b hn).commonNeighbors c d) ≤
      Nat.card (G.commonNeighbors c.val d.val)+1 := by
  classical
  let X := (merge G a b hn).commonNeighbors c d
  let Y := G.commonNeighbors c.val d.val
  have hneigh (x : X) (hx : x.val.val ≠ a) : x.val.val ∈ Y := by
    have h : (merge G a b hn).Adj c x.val ∧
        (merge G a b hn).Adj d x.val := x.property
    have hc := (merge_adj G a b hn c x.val).mp h.1
    have hd := (merge_adj G a b hn d x.val).mp h.2
    exact ⟨by simpa only [hca,hx,false_and,or_false] using hc,
      by simpa only [hda,hx,false_and,or_false] using hd⟩
  let f : X → Option Y := fun x => if hx : x.val.val = a then none
    else some ⟨x.val.val,hneigh x hx⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    by_cases hx : x.val.val = a
    · by_cases hy : y.val.val = a
      · exact hx.trans hy.symm
      · simp [f,hx,hy] at hxy
    · by_cases hy : y.val.val = a
      · simp [f,hx,hy] at hxy
      · have he : (⟨x.val.val,hneigh x hx⟩ : Y) = ⟨y.val.val,hneigh y hy⟩ := by
          simpa only [f,dif_neg hx,dif_neg hy,Option.some.injEq] using hxy
        exact congrArg (fun z : Y => z.val) he
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option,X,Y] using hh

lemma double_merge_edge_bound [Fintype V] (G : SimpleGraph V) {a b : V}
    (hab : a ≠ b) (hn : ¬ G.Adj a b) (c d : {x : V // x ≠ b})
    (hca : c.val ≠ a) (hda : d.val ≠ a) (hcd : c ≠ d)
    (hncd : ¬ (merge G a b hn).Adj c d) :
    Nat.card G.edgeSet ≤ Nat.card (merge (merge G a b hn) c d hncd).edgeSet+
      Nat.card (G.commonNeighbors a b)+Nat.card (G.commonNeighbors c.val d.val)+1 := by
  classical
  have hfirst := merge_edge_count G hab hn
  have hsecond := merge_edge_count (merge G a b hn) hcd hncd
  have hover := common_after_merge_le G a b hn c d hca hda
  omega

lemma safe_double_merge_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {a b : V} (hab : a ≠ b) (hn : ¬ G.Adj a b) (c d : {x : V // x ≠ b})
    (hca : c.val ≠ a) (hda : d.val ≠ a) (hcd : c ≠ d)
    (hncd : ¬ (merge G a b hn).Adj c d)
    (hf : H.Free (merge (merge G a b hn) c d hncd)) :
    Nat.card G.edgeSet ≤ extremalNumber (Fintype.card V-2) H+
      Nat.card (G.commonNeighbors a b)+Nat.card (G.commonNeighbors c.val d.val)+1 := by
  classical
  have hb := safe_merge_bound H (merge G a b hn) hcd hncd hf
  have hfirst := merge_edge_count G hab hn
  have hover := common_after_merge_le G a b hn c d hca hda
  have hcard : Fintype.card {x : V // x ≠ b} = Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hcard,Nat.sub_sub,show 1+1=2 from rfl] at hb
  omega

#print axioms common_after_merge_le
#print axioms double_merge_edge_bound
#print axioms safe_double_merge_bound
end Erdos713DoubleMergeCost
