import FormalConjecturesUtil
import Submission.ContractionOddCycles
import Submission.SplitEdgePacking

/-! Robust edge-rooted contraction witnesses. Split copies avoid both the
specified root edge and an arbitrary small deleted edge set. Packings are
edge-disjoint, not necessarily internally vertex-disjoint. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713RobustContractionWitnesses
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
open Erdos713EdgeContraction Erdos713RobustMergeWitnesses
open Erdos713SplitEdgePacking Erdos713ContractionOddCycles
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma contract_after_deleting [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1 <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) :
    H ⊑ contract (G.deleteEdges (T : Set (Sym2 V))) u v := by
  let K := G.deleteEdges (T : Set (Sym2 V))
  have hle : eraseEdge K u v ≤ G := (eraseEdge_le K u v).trans (G.deleteEdges_le _)
  have h1 := delete_edge_loss G T
  have h2 := delete_edge_loss K {s(u,v)}
  simp only [card_singleton,coe_singleton] at h2
  change Nat.card G.edgeSet ≤ Nat.card K.edgeSet+T.card at h1
  change Nat.card K.edgeSet ≤ Nat.card (eraseEdge K u v).edgeSet+1 at h2
  have hLoss : Nat.card G.edgeSet ≤ Nat.card (eraseEdge K u v).edgeSet+(T.card+1) := by omega
  apply merge_after_loss H G _ he hle hLoss huv (eraseEdge_not_adj K u v)
  simpa only [Nat.cast_add,Nat.cast_one,add_right_comm] using hsmall

lemma split_after_deleting [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1 <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) :
    ∃ (w : W) (S : Set W)
      (f : (split H w S).Copy (eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v)),
      f (some w) = u ∧ f none = v ∧
      (∃ x, H.Adj w x ∧ x ∈ S) ∧ (∃ y, H.Adj w y ∧ y ∉ S) := by
  have hle : eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v ≤ G :=
    (eraseEdge_le _ u v).trans (G.deleteEdges_le _)
  apply split_copy_of_merge (fun h => hf (h.trans ⟨Copy.ofLE _ _ hle⟩))
    (eraseEdge_not_adj _ u v)
  exact contract_after_deleting H G he huv T hsmall

lemma witness_avoiding [Fintype V] [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (hf : H.Free G) (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1 <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) :
    ∃ f : Witness H G u v, Disjoint f.edges (insert s(u,v) T) := by
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_after_deleting H G hf he huv T hsmall
  have hle : eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v ≤ G :=
    (eraseEdge_le _ u v).trans (G.deleteEdges_le _)
  let g := (Copy.ofLE _ _ hle).comp f
  let F : Witness H G u v := ⟨w,S,g,hu,hv,hL,hR⟩
  refine ⟨F,Finset.disjoint_left.mpr ?_⟩
  intro e he hT
  obtain ⟨e0,he0,rfl⟩ := Finset.mem_image.mp he
  induction e0 using Sym2.ind with | _ x y =>
  have ha := f.toHom.map_adj (mem_edgeFinset.mp he0)
  have ha' := deleteEdges_adj.mp ha
  have ha'' := deleteEdges_adj.mp ha'.1
  rcases mem_insert.mp hT with hroot | hT
  · exact ha'.2 hroot
  · exact ha''.2 hT

/-- Each split witness omits the root edge. Adjacent roots are allowed. -/
def RobustEdgeRoots [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (u v : V) (t : ℝ) : Prop :=
  ∀ T : Finset (Sym2 V), (T.card : ℝ) ≤ t →
    ∃ f : Witness H G u v, Disjoint f.edges (insert s(u,v) T)

lemma robust_of_backward_gap [Fintype V] [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) {t s : ℝ}
    (hgap : t+s+1 < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ))
    (hcodeg : (Nat.card (G.commonNeighbors u v) : ℝ) ≤ s) :
    RobustEdgeRoots H G u v t := by
  intro T hT
  exact witness_avoiding H G hf he huv T (by linarith)

lemma packing_of_robust [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (u v : V) {t : ℝ} (h : RobustEdgeRoots H G u v t) (k : ℕ)
    (hk : (k*(Fintype.card W+1).choose 2 : ℕ) ≤ t) : EdgePacking H G u v k := by
  apply packing_of_avoidance H G u v k
  intro T hT
  have hTR : (T.card : ℝ) ≤ (k*(Fintype.card W+1).choose 2 : ℕ) := by exact_mod_cast hT
  obtain ⟨f,hf⟩ := h T (hTR.trans hk)
  exact ⟨f,hf.mono_right (subset_insert _ _)⟩

/-- Robust even alternative paths, for patterns that remain preconnected
when one vertex is removed. Adding the root edge gives an odd cycle. -/
theorem even_path_after_deleting [Fintype V] [Fintype W]
    {H : SimpleGraph W} (hH : H.IsBipartite)
    (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected) {G : SimpleGraph V} (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1 <
      (extremalNumber (Fintype.card V) H : ℝ)-
        (extremalNumber (Fintype.card V-1) H : ℝ)) :
    ∃ p : G.Walk v u, p.IsPath ∧ Even p.length ∧ p.length ≤ Fintype.card W ∧
      s(u,v) ∉ p.edges ∧ ∀ e ∈ p.edges, e ∉ T := by
  have hle := G.deleteEdges_le (T : Set (Sym2 V))
  have hfK : H.Free (G.deleteEdges (T : Set (Sym2 V))) :=
    fun h => hf (h.trans ⟨Copy.ofLE _ _ hle⟩)
  obtain ⟨p,hp,hEven,hLen,hRoot⟩ := even_alternative_of_contract hH hRest hfK
    (contract_after_deleting H G he huv T hsmall)
  refine ⟨p.mapLe hle,hp.mapLe _,?_,?_,?_,?_⟩
  · simpa using hEven
  · simpa using hLen
  · simpa only [Walk.edges_mapLe_eq_edges] using hRoot
  · intro e he hT
    have he' : e ∈ p.edges := by simpa only [Walk.edges_mapLe_eq_edges] using he
    have heG := p.edges_subset_edgeSet he'
    induction e using Sym2.ind with | _ x y =>
    have ha : (G.deleteEdges (T : Set (Sym2 V))).Adj x y := by simpa using heG
    exact (deleteEdges_adj.mp ha).2 hT

#print axioms contract_after_deleting
#print axioms witness_avoiding
#print axioms packing_of_robust
#print axioms even_path_after_deleting
end Erdos713RobustContractionWitnesses
