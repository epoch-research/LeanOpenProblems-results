import FormalConjecturesUtil
import Submission.MergeDegreePenalty
import Submission.RobustContractionWitnesses
import Submission.C8SplitPaths

/-! Contraction comparisons on globally degree-penalized hosts.
No exact edge maximality or extremal consecutive difference is assumed. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713PenalizedContraction
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713MergeDegreePenalty
open Erdos713VertexMerging Erdos713VertexSplitWitnesses Erdos713EdgeContraction
open Erdos713RobustMergeWitnesses Erdos713SplitEdgePacking
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma energy_mono [Fintype V] {F G : SimpleGraph V} (h : F ≤ G) :
    energy F ≤ energy G := by
  apply sum_le_sum
  intro v _
  exact pow_le_pow_left₀ (degreeR_nonneg _ _) (degreeR_mono h v) 2

/-- The cost includes edge loss before merging, and an upper bound for the
increase of the squared-degree energy. -/
lemma safe_merge_after_loss [Fintype V] {H : SimpleGraph W} {G F : SimpleGraph V}
    {lam mu t : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    (hle : F ≤ G) (hloss : edgesR G ≤ edgesR F+t)
    {u v : V} (huv : u ≠ v) (hn : ¬F.Adj u v)
    (hf : H.Free (merge F u v hn)) :
    mu*(2*Fintype.card V-1) ≤ t+(Nat.card (G.commonNeighbors u v) : ℝ)+
      2*lam*degreeR G u*degreeR G v := by
  have hh := hg.compare_graph (merge F u v hn) hf
  have hcard : Fintype.card {x : V // x ≠ v}=Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  unfold potential score at hh
  rw [hcard,Nat.cast_sub hpos,Nat.cast_one] at hh
  have he : edgesR (merge F u v hn)+(Nat.card (F.commonNeighbors u v) : ℝ)=edgesR F := by
    unfold edgesR
    exact_mod_cast merge_edge_count F huv hn
  have hcom : (Nat.card (F.commonNeighbors u v) : ℝ) ≤ Nat.card (G.commonNeighbors u v) :=
    Nat.cast_le.mpr (common_card_mono hle u v)
  have hprod := mul_le_mul (degreeR_mono hle u) (degreeR_mono hle v)
    (degreeR_nonneg _ _) (degreeR_nonneg _ _)
  have henergy : energy (merge F u v hn) ≤ energy G+2*degreeR G u*degreeR G v := by
    have hm := merge_energy F huv hn
    have heF := energy_mono hle
    nlinarith only [hm,heF,hprod]
  have henergy' := mul_le_mul_of_nonneg_left henergy hlam
  nlinarith only [hh,he,hcom,hloss,henergy']

lemma contract_after_deleting [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
      2*lam*degreeR G u*degreeR G v < mu*(2*Fintype.card V-1)) :
    H ⊑ contract (G.deleteEdges (T : Set (Sym2 V))) u v := by
  let K := G.deleteEdges (T : Set (Sym2 V))
  have hle : eraseEdge K u v ≤ G := (eraseEdge_le K u v).trans (G.deleteEdges_le _)
  have h1 := delete_edge_loss G T
  have h2 := delete_edge_loss K {s(u,v)}
  simp only [card_singleton,coe_singleton] at h2
  change Nat.card G.edgeSet ≤ Nat.card K.edgeSet+T.card at h1
  change Nat.card K.edgeSet ≤ Nat.card (eraseEdge K u v).edgeSet+1 at h2
  have hLoss : edgesR G ≤ edgesR (eraseEdge K u v)+(T.card+1) := by
    unfold edgesR
    exact_mod_cast (show Nat.card G.edgeSet ≤ Nat.card (eraseEdge K u v).edgeSet+(T.card+1) by omega)
  by_contra hf
  have hb := safe_merge_after_loss hg hlam hle hLoss huv (eraseEdge_not_adj K u v) hf
  linarith

lemma split_after_deleting [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
      2*lam*degreeR G u*degreeR G v < mu*(2*Fintype.card V-1)) :
    ∃ (w : W) (S : Set W)
      (f : (split H w S).Copy (eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v)),
      f (some w) = u ∧ f none = v ∧
      (∃ x, H.Adj w x ∧ x ∈ S) ∧ (∃ y, H.Adj w y ∧ y ∉ S) := by
  have hle : eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v ≤ G :=
    (eraseEdge_le _ u v).trans (G.deleteEdges_le _)
  apply split_copy_of_merge (fun h => hg.free (h.trans ⟨Copy.ofLE _ _ hle⟩))
    (eraseEdge_not_adj _ u v)
  exact contract_after_deleting hg hlam huv T hsmall

lemma witness_avoiding [Fintype V] [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    {u v : V} (huv : u ≠ v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
      2*lam*degreeR G u*degreeR G v < mu*(2*Fintype.card V-1)) :
    ∃ f : Witness H G u v, Disjoint f.edges (insert s(u,v) T) := by
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_after_deleting hg hlam huv T hsmall
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

lemma robust_of_penalty [Fintype V] [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu t s : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    {u v : V} (huv : u ≠ v)
    (hgap : t+s+1 < mu*(2*Fintype.card V-1))
    (hcost : (Nat.card (G.commonNeighbors u v) : ℝ)+2*lam*degreeR G u*degreeR G v ≤ s) :
    Erdos713RobustContractionWitnesses.RobustEdgeRoots H G u v t := by
  intro T hT
  exact witness_avoiding hg hlam huv T (by linarith)

theorem nine_cycle_after_deleting {V : Type*} [Fintype V] {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal (cycleGraph 8) G lam mu) (hlam : 0 ≤ lam)
    {u v : V} (huv : G.Adj u v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
      2*lam*degreeR G u*degreeR G v < mu*(2*Fintype.card V-1)) :
    ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 9 ∧ s(u,v) ∈ p.edges ∧
      ∀ e ∈ p.edges, e ≠ s(u,v) → e ∉ T := by
  classical
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_after_deleting hg hlam huv.ne T hsmall
  obtain ⟨p,hp,hLen⟩ := Erdos713C8SplitPaths.split_has_path_eight w S hL hR
  let K := eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v
  have hle : K ≤ G := (eraseEdge_le _ u v).trans (G.deleteEdges_le _)
  let p0 : K.Walk v u := (p.map f.toHom).copy hv hu
  have hp0 : p0.IsPath :=
    (Walk.isPath_copy _ hv hu).mpr (Walk.map_isPath_of_injective f.injective hp)
  have hlen0 : p0.length = 8 := by simpa only [p0,Walk.length_copy,Walk.length_map] using hLen
  let pG : G.Walk v u := p0.mapLe hle
  have hpG : pG.IsPath := hp0.mapLe hle
  have hlenG : pG.length = 8 := by simpa [pG] using hlen0
  have hAvoid : ∀ e ∈ pG.edges, e ≠ s(u,v) ∧ e ∉ T := by
    intro e he
    have he0 : e ∈ p0.edges := by simpa only [pG,Walk.edges_mapLe_eq_edges] using he
    have heK := p0.edges_subset_edgeSet he0
    induction e using Sym2.ind with | _ x y =>
    have ha : K.Adj x y := by simpa using heK
    have ha' := deleteEdges_adj.mp ha
    exact ⟨ha'.2,(deleteEdges_adj.mp ha'.1).2⟩
  have hRoot : s(u,v) ∉ pG.edges := fun h => (hAvoid _ h).1 rfl
  refine ⟨Walk.cons huv pG,(Walk.cons_isCycle_iff pG huv).mpr ⟨hpG,hRoot⟩,?_,?_,?_⟩
  · simp only [Walk.length_cons,hlenG]
  · simp only [Walk.edges_cons,List.mem_cons,true_or]
  · intro e he hne
    have he' : e = s(u,v) ∨ e ∈ pG.edges := by simpa only [Walk.edges_cons,List.mem_cons] using he
    exact (hAvoid _ (he'.resolve_left hne)).2


/-- A budget at one C8-free host yields robust C9 witnesses and an
edge-disjoint split packing at the very same roots. -/
lemma c8_edge_witnesses [Fintype V] {G : SimpleGraph V} {lam mu t : ℝ}
    (hg : GlobalOptimal (cycleGraph 8) G lam mu) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    {u v : V} (huv : G.Adj u v)
    (hcost : t+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
      2*lam*degreeR G u*degreeR G v < mu*(2*Fintype.card V-1)) :
    Erdos713RobustContractionWitnesses.RobustEdgeRoots (cycleGraph 8) G u v t ∧
    EdgePacking (cycleGraph 8) G u v ⌊t/36⌋₊ ∧
    ∀ T : Finset (Sym2 V), (T.card : ℝ) ≤ t →
      ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 9 ∧ s(u,v) ∈ p.edges ∧
        ∀ e ∈ p.edges, e ≠ s(u,v) → e ∉ T := by
  have hr : Erdos713RobustContractionWitnesses.RobustEdgeRoots (cycleGraph 8) G u v t := by
    intro T hT
    exact witness_avoiding hg hlam huv.ne T (by linarith)
  refine ⟨hr,?_,?_⟩
  · apply Erdos713RobustContractionWitnesses.packing_of_robust (cycleGraph 8) G u v hr
    have hflo := Nat.floor_le (show 0 ≤ t/36 by positivity)
    norm_num only [Fintype.card_fin,Nat.reduceAdd,Nat.choose] at ⊢
    push_cast
    nlinarith only [hflo]
  · intro T hT
    exact nine_cycle_after_deleting hg hlam huv T (by linarith)

#print axioms robust_of_penalty
#print axioms nine_cycle_after_deleting
#print axioms c8_edge_witnesses
end Erdos713PenalizedContraction
