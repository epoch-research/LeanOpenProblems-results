import FormalConjecturesUtil
import Submission.VertexSplitWitnesses

/-! Low-overlap merger obstructions survive edge deletions below the
backward extremal gap. No rate for the split pattern is needed. -/
open SimpleGraph Finset
namespace Erdos713RobustMergeWitnesses
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma safe_merge_bound [Fintype V] (H : SimpleGraph W) (F : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (hn : ¬ F.Adj u v) (hf : H.Free (merge F u v hn)) :
    Nat.card F.edgeSet ≤ extremalNumber (Fintype.card V-1) H +
      Nat.card (F.commonNeighbors u v) := by
  classical
  have hc : Fintype.card {x : V // x ≠ v} = Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hb := card_edgeFinset_le_extremalNumber hf
  rw [hc] at hb
  have he := merge_edge_count F huv hn
  simp only [edgeFinset_card,Nat.card_eq_fintype_card] at hb he ⊢
  omega

lemma common_card_mono [Fintype V] {F G : SimpleGraph V} (hle : F ≤ G) (u v : V) :
    Nat.card (F.commonNeighbors u v) ≤ Nat.card (G.commonNeighbors u v) := by
  apply Nat.card_le_card_of_injective
    (fun x : F.commonNeighbors u v =>
      (⟨x.val,hle x.property.1,hle x.property.2⟩ : G.commonNeighbors u v))
  intro x y h
  exact Subtype.ext (congrArg (fun z : G.commonNeighbors u v => z.val) h)

lemma delete_edge_loss [Fintype V] (G : SimpleGraph V) (T : Finset (Sym2 V)) :
    Nat.card G.edgeSet ≤ Nat.card (G.deleteEdges (T : Set (Sym2 V))).edgeSet + T.card := by
  classical
  have hh := Finset.le_card_sdiff (t := G.edgeFinset) (s := T)
  rw [← edgeFinset_deleteEdges] at hh
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using (Nat.sub_le_iff_le_add.mp hh)

lemma merge_after_loss [Fintype V] (H : SimpleGraph W) (G F : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (hle : F ≤ G) {t : ℕ} (hloss : Nat.card G.edgeSet ≤ Nat.card F.edgeSet+t)
    {u v : V} (huv : u ≠ v) (hn : ¬ F.Adj u v)
    (hsmall : (t : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) : H ⊑ merge F u v hn := by
  by_contra hh
  have hb := safe_merge_bound H F huv hn hh
  have hcom := common_card_mono hle u v
  have hN : extremalNumber (Fintype.card V) H ≤
      extremalNumber (Fintype.card V-1) H+Nat.card (G.commonNeighbors u v)+t := by omega
  have hR : (extremalNumber (Fintype.card V) H : ℝ) ≤
      (extremalNumber (Fintype.card V-1) H : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+t := by
    exact_mod_cast hN
  linarith

/-- Robustness is for edge deletions, NOT deletion of arbitrary internal
vertices. The split type may depend on the deleted edge set. -/
theorem split_after_deleting [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ) <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) :
    ∃ (w : W) (S : Set W) (f : (split H w S).Copy (G.deleteEdges (T : Set (Sym2 V)))),
      f (some w) = u ∧ f none = v ∧
      (∃ x, H.Adj w x ∧ x ∈ S) ∧ (∃ y, H.Adj w y ∧ y ∉ S) := by
  have hle := G.deleteEdges_le (T : Set (Sym2 V))
  have hnF : ¬ (G.deleteEdges (T : Set (Sym2 V))).Adj u v := fun h => hn (hle h)
  apply split_copy_of_merge (fun h => hf (h.trans ⟨Copy.ofLE _ _ hle⟩)) hnF
  exact merge_after_loss H G _ he hle (delete_edge_loss G T) huv hnF hsmall

#print axioms safe_merge_bound
#print axioms merge_after_loss
#print axioms split_after_deleting
end Erdos713RobustMergeWitnesses
