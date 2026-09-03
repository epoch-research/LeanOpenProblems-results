import Submission.EdgeAveraging

/-!
A local extremal bound can be averaged over an edge-transitive host. The
result is a relative-density bound, not a solution of Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
namespace Erdos714LocalAveraging
variable {V W Z : Type*} [Fintype V] [Fintype W]

/-- Use only the edges of the copied block, even when the block is not induced. -/
lemma translated_block_bound (F : SimpleGraph Z) (H G : SimpleGraph V)
    (A : SimpleGraph W) (c : A.Copy G)
    (hH : F.Free H) (b : ℕ)
    (hb : ∀ J : SimpleGraph W, J ≤ A → F.Free J → J.edgeFinset.card ≤ b)
    (g : G ≃g G) :
    ((univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)).filter
      (fun e => e ∈ Erdos714Averaging.translate (Erdos714GraphAveraging.edgeAction G) g
        (univ.map c.mapEdgeSet))).card ≤ b := by
  let f : W ↪ V := c.toEmbedding.trans g.toEquiv.toEmbedding
  let J : SimpleGraph W := A ⊓ H.comap f
  have hJfree : F.Free J := by
    intro hc
    exact (Erdos714GraphAveraging.free_comap F H f hH) (hc.mono_right inf_le_right)
  have hJbound : J.edgeFinset.card ≤ b := by
    simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hb J inf_le_left hJfree
  apply (show _ ≤ J.edgeFinset.card from ?_).trans hJbound
  rw [Erdos714Averaging.translate, Finset.map_map]
  rw [Erdos714GraphAveraging.filter_image_card
    (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)) univ
    (c.mapEdgeSet.trans ((Erdos714GraphAveraging.edgeAction G) g).toEmbedding)]
  apply Finset.card_le_card_of_injOn (fun e : A.edgeSet => e.val)
  · intro e he
    change e.val ∈ J.edgeFinset
    rw [mem_edgeFinset]
    have hm := (mem_filter.mp he).2
    change Erdos714GraphAveraging.edgeAction G g (c.mapEdgeSet e) ∈
      univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet) at hm
    have hm' := (mem_filter.mp hm).2
    change Sym2.map g (Sym2.map c e.val) ∈ H.edgeSet at hm'
    rw [Sym2.map_map] at hm'
    rw [show J.edgeSet = A.edgeSet ∩ (H.comap f).edgeSet from edgeSet_inf _ _]
    refine ⟨e.property, ?_⟩
    rcases e with ⟨e,he⟩
    induction e using Sym2.ind with
    | _ x y => exact hm'
  · intro e _ e' _ hh
    exact Subtype.ext hh

/-- A fixed finite block yields its local retained fraction as a global bound. -/
theorem edge_transitive_local_bound (F : SimpleGraph Z) (H G : SimpleGraph V)
    (A : SimpleGraph W) (c : A.Copy G) (hHG : H ≤ G) (hH : F.Free H)
    (htrans : Erdos714GraphAveraging.EdgeTransitive G)
    (b : ℕ) (hb : ∀ J : SimpleGraph W, J ≤ A → F.Free J → J.edgeFinset.card ≤ b) :
    A.edgeFinset.card * H.edgeFinset.card ≤ b * G.edgeFinset.card := by
  letI : Fintype (G ≃g G) := Fintype.ofInjective RelIso.toEquiv RelIso.toEquiv_injective
  have h := Erdos714Averaging.transitive_bound (Erdos714GraphAveraging.edgeAction G) htrans
    (univ.map c.mapEdgeSet) (univ.filter (fun e : G.edgeSet => e.val ∈ H.edgeSet)) b
    (translated_block_bound F H G A c hH b hb)
  simpa only [Finset.card_map, Finset.card_univ,
    Erdos714GraphAveraging.selected_edge_card H G hHG, SimpleGraph.card_edgeSet] using h

#print axioms translated_block_bound
#print axioms edge_transitive_local_bound
end Erdos714LocalAveraging
