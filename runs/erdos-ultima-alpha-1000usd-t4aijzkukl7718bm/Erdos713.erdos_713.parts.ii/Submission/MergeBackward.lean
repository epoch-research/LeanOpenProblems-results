import FormalConjecturesUtil
import Submission.VertexMerging

/-! A backward extremal increment alone supplies a merger obstruction. -/
open SimpleGraph
namespace Erdos713MergeBackward
open Erdos713VertexMerging
variable {V W : Type*}

lemma safe_merge_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) (hsafe : H.Free (merge G u v hn)) :
    Nat.card G.edgeSet ≤ extremalNumber (Fintype.card V-1) H+Nat.card (G.commonNeighbors u v) := by
  classical
  have hc : Fintype.card {x : V // x ≠ v} = Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hbound : Nat.card (merge G u v hn).edgeSet ≤ extremalNumber (Fintype.card V-1) H := by
    have hh := card_edgeFinset_le_extremalNumber hsafe
    rw [hc] at hh
    simpa only [edgeFinset_card,Nat.card_eq_fintype_card] using hh
  have hedge := merge_edge_count G huv hn
  omega

lemma merge_contains_of_backward [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H) {s : ℝ}
    (hgap : s < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ))
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v)
    (hsmall : (Nat.card (G.commonNeighbors u v) : ℝ) ≤ s) : H ⊑ merge G u v hn := by
  by_contra hh
  have hb := safe_merge_bound H G huv hn hh
  rw [he] at hb
  have hbR : (extremalNumber (Fintype.card V) H : ℝ) ≤
      (extremalNumber (Fintype.card V-1) H : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) := by
    exact_mod_cast hb
  linarith

#print axioms merge_contains_of_backward
end Erdos713MergeBackward
