import Submission.TwoRunCompression

/-! Combined cycle-and-tail run compression for a normal component. The
branching root and tail finish must be retained, and the compressed cycle
must have at least three vertices. All cardinal costs are explicit. -/
namespace Erdos583LollipopFullRunCompressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion Erdos583Work.MemberComponents
open Erdos583CycleRunIntervalsDevelopment Erdos583PathRunIntervalsDevelopment
open Erdos583PrivatePathExpansionDevelopment Erdos583RunCompressionDataDevelopment
open Erdos583TwoRunCompressionDevelopment Erdos583LollipopRunSuppressionDevelopment
open Erdos583TailRunFreshnessDevelopment Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V} {r b : V}

lemma lollipop_run_graph_form (C : G.Walk r r) (P : G.Walk r b) (S : Set V)
    (hr : r ∉ S) (hb : b ∉ S) (F : SimpleGraph V)
    (hCF : C.toSubgraph.spanningCoe ≤ F) (hPF : P.toSubgraph.spanningCoe ≤ F)
    (hF : ∀ x ∈ S, ∀ y, F.Adj x y ↔ C.toSubgraph.Adj x y ∨ P.toSubgraph.Adj x y) :
    F=(within F Sᶜ ⊔ arcs (runs C S) (runPath C)) ⊔ arcs (runs P S) (runPath P) := by
  have hit {x y : V} (hxy : F.Adj x y) (hx : x ∈ S) :
      (arcs (runs C S) (runPath C)).Adj x y ∨ (arcs (runs P S) (runPath P)).Adj x y := by
    rcases (hF x hx y).mp hxy with hh|hh
    · obtain ⟨p,hp,he⟩ := runs_cover_inside_edges C S hr hh (Or.inl hx)
      exact Or.inl ((arcs_adj _ _ _ _).mpr ⟨p,hp,he⟩)
    · obtain ⟨p,hp,he⟩ := path_runs_cover_inside_edges P S hr hb hh (Or.inl hx)
      exact Or.inr ((arcs_adj _ _ _ _).mpr ⟨p,hp,he⟩)
  ext x y
  constructor
  · intro hxy
    by_cases hx : x ∈ S
    · rcases hit hxy hx with hh|hh
      · exact Or.inl (Or.inr hh)
      · exact Or.inr hh
    by_cases hy : y ∈ S
    · rcases hit hxy.symm hy with hh|hh
      · exact Or.inl (Or.inr hh.symm)
      · exact Or.inr hh.symm
    exact Or.inl (Or.inl ⟨hxy,hx,hy⟩)
  · rintro ((hxy|hxy)|hxy)
    · exact hxy.1
    · obtain ⟨p,_,hxy⟩ := (arcs_adj _ _ _ _).mp hxy
      exact hCF (show C.toSubgraph.Adj x y from runPath_edges_subset C p
        (show s(x,y) ∈ (runPath C p).toSubgraph.edgeSet from hxy))
    · obtain ⟨p,_,hxy⟩ := (arcs_adj _ _ _ _).mp hxy
      exact hPF (show P.toSubgraph.Adj x y from runPath_edges_subset P p
        (show s(x,y) ∈ (runPath P p).toSubgraph.edgeSet from hxy))

lemma lollipop_run_partition [Fintype V] {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (C : G.Walk r r) (P : G.Walk r b) (hC : C.IsCycle) (hP : P.IsPath)
    (hinter : ∀ z ∈ C.support, z ∈ P.support → z=r)
    (S : Set V) (hr : r ∉ S) (hb : b ∉ S)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < C.length)
    (ht : C.getVert t ∉ S) (hu : C.getVert u ∉ S)
    (F : SimpleGraph V) (hCF : C.toSubgraph.spanningCoe ≤ F) (hPF : P.toSubgraph.spanningCoe ≤ F)
    (hF : ∀ x ∈ S, ∀ y, F.Adj x y ↔ C.toSubgraph.Adj x y ∨ P.toSubgraph.Adj x y)
    (hfC : ∀ p ∈ runs C S, ¬(within F Sᶜ).Adj (runStart C p) (runFinish C p))
    (hfP : ∀ p ∈ runs P S, ¬(within F Sᶜ).Adj (runStart P p) (runFinish P p))
    (hc : SupportConnected F) (hsize : Sᶜ.ncard < n) :
    ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
  have hform := lollipop_run_graph_form C P S hr hb F hCF hPF hF
  obtain ⟨D,hD,hDc⟩ := two_run_partition hsmall C P S hr hinter
    (cycle_run_conditions C hC S hr ht0 htu huN ht hu) (path_run_conditions P hP S)
    (within F Sᶜ) (within_support F Sᶜ) hfC hfP (hform ▸ hc) hsize
  exact partition_transport hform.symm ⟨D,hD,hDc⟩

lemma no_compressible_normal_component {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (root : Fin n) (L : RootedCycleRep T root)
    (hCmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W root,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (hPmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W root,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    (A : (normalGraph T L.index).ConnectedComponent)
    (S : Set (Fin n)) (hSA : S ⊆ (selectedGraph T (componentMembers T L.index A)).support)
    (hSn : S.Nonempty) (hr : root ∉ S) (hb : L.finish ∉ S)
    (hout : 3 ≤ (L.cycle.toSubgraph.verts \ S).ncard)
    (hbudget : (componentMembers T L.index A).card+⌈(Sᶜ.ncard : ℚ)/2⌉₊ ≤
      ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) : False := by
  let B := componentMembers T L.index A
  let F := selectedGraph T (Finset.univ \ B)
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hFc := complement_connected T hG L.index hn A
  have hCF : L.cycle.toSubgraph.spanningCoe ≤ F := by
    intro x y hxy
    refine ⟨L.index,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T L.index A⟩,?_⟩
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    exact Or.inl hxy
  have hPF : L.tail.toSubgraph.spanningCoe ≤ F := by
    intro x y hxy
    refine ⟨L.index,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T L.index A⟩,?_⟩
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    exact Or.inr hxy
  have hF : ∀ x ∈ S, ∀ y, F.Adj x y ↔ L.cycle.toSubgraph.Adj x y ∨ L.tail.toSubgraph.Adj x y := by
    intro x hx y
    rw [complement_adj_at T L.index A (hSA hx),L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hSp := hSn.ncard_pos
  obtain ⟨t,u,ht0,htu,huN,ht,hu⟩ := two_ordered_outside_marks L.cycle S hr hout
  obtain ⟨D,hD,hDc⟩ := lollipop_run_partition hsmall L.cycle L.tail L.isCycle L.isPath L.inter
    S hr hb ht0 htu huN ht hu F hCF hPF hF
    (subset_runs_fresh T hs root L hCmin A S hSA ht0 htu huN ht hu)
    (subset_tail_runs_fresh T hs root L hPmin A S hSA) hFc (by omega)
  have hp (j) (hj : j ∉ Finset.univ \ B) : (T.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      ((mem_componentMembers T L.index j A).mp hjB).1
  obtain ⟨E,hE,hEc⟩ := replace_selected T (Finset.univ \ B) hp D hD
  have hcard : (Finset.univ \ B).card=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hcard] at hEc
  change B.card+⌈(Sᶜ.ncard : ℚ)/2⌉₊ ≤ _ at hbudget
  omega

end Erdos583LollipopFullRunCompressionDevelopment
