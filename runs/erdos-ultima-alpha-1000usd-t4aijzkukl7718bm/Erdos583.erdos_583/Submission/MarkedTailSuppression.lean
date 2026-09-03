import Submission.MarkedPrefixRunCompression
import Submission.UnifiedMinimalDefect

/-! A strict-half suppression criterion when the final tail endpoint is in
the deleted component but the entire cycle is retained. -/
namespace Erdos583MarkedTailSuppressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583CycleRunIntervalsDevelopment Erdos583PathRunIntervalsDevelopment
open Erdos583PrivatePathExpansionDevelopment Erdos583RunCompressionDataDevelopment
open Erdos583MarkedPrefixRunCompressionDevelopment Erdos583TailPrefixRunFreshnessDevelopment
open Erdos583NormalComponentComplementDevelopment Erdos583TwoRunCompressionDevelopment
open Erdos583UnifiedMinimalDefectDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma prefix_run_graph_form {V : Type*} {G : SimpleGraph V} {a w b : V}
    (W : G.Walk a w) (Q : G.Walk w b) (S : Set V) (ha : a ∉ S) (hw : w ∉ S)
    (H : SimpleGraph V) (hP : (W.append Q).toSubgraph.spanningCoe ≤ H)
    (hH : ∀ x ∈ S, ∀ y, H.Adj x y ↔ (W.append Q).toSubgraph.Adj x y) :
    H=(within H Sᶜ ⊔ arcs (runs W S) (runPath W)) ⊔ Q.toSubgraph.spanningCoe := by
  have hit {x y : V} (hxy : H.Adj x y) (hx : x ∈ S) :
      (arcs (runs W S) (runPath W)).Adj x y ∨ Q.toSubgraph.Adj x y := by
    have he := (hH x hx y).mp hxy
    rw [Walk.toSubgraph_append,Subgraph.sup_adj] at he
    rcases he with he|he
    · obtain ⟨p,hp,he⟩ := path_runs_cover_inside_edges W S ha hw he (Or.inl hx)
      exact Or.inl ((arcs_adj _ _ _ _).mpr ⟨p,hp,he⟩)
    · exact Or.inr he
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
    · apply hP
      change (W.append Q).toSubgraph.Adj x y
      rw [Walk.toSubgraph_append,Subgraph.sup_adj]
      obtain ⟨p,_,hxy⟩ := (arcs_adj _ _ _ _).mp hxy
      exact Or.inl (show W.toSubgraph.Adj x y from runPath_edges_subset W p
        (show s(x,y) ∈ (runPath W p).toSubgraph.edgeSet from hxy))
    · apply hP
      change (W.append Q).toSubgraph.Adj x y
      rw [Walk.toSubgraph_append,Subgraph.sup_adj]
      exact Or.inr hxy

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma no_compressible_terminal_component
    (A : (normalGraph D.family D.rep.index).ConnectedComponent)
    (hcycle : Disjoint D.rep.cycle.toSubgraph.verts
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support)
    (hfinish : D.rep.finish ∈ (selectedGraph D.family (componentMembers D.family D.rep.index A)).support)
    (hc : SupportConnected (within (selectedGraph D.family (Finset.univ \
      componentMembers D.family D.rep.index A))
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).supportᶜ))
    (hcore : (within (selectedGraph D.family (Finset.univ \
      componentMembers D.family D.rep.index A))
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).supportᶜ).support=
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).supportᶜ)
    (hhalf : 2*(selectedGraph D.family (componentMembers D.family D.rep.index A)).supportᶜ.ncard < F.order)
    (hbudget : (componentMembers D.family D.rep.index A).card+
      ⌈((selectedGraph D.family (componentMembers D.family D.rep.index A)).supportᶜ.ncard : ℚ)/2⌉₊ ≤
      budget F.order) : False := by
  let B := componentMembers D.family D.rep.index A
  let S := (selectedGraph D.family B).support
  let H := selectedGraph D.family (Finset.univ \ B)
  let H₀ := within H Sᶜ
  have hr : D.root ∉ S := fun hh ↦ Set.disjoint_left.mp hcycle D.rep.cycle.start_mem_verts_toSubgraph hh
  obtain ⟨w,hw,W,Q,hform,hQlast⟩ := CycleDefect.last_hit_split D.rep.tail Sᶜ
    ⟨D.root,D.rep.tail.start_mem_support,hr⟩
  have hp : (W.append Q).IsPath := hform ▸ D.rep.isPath
  have hP : (W.append Q).toSubgraph.spanningCoe ≤ H := by
    intro x y hxy
    refine ⟨D.rep.index,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem D.family D.rep.index A⟩,?_⟩
    rw [D.rep.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    exact Or.inr (hform ▸ hxy)
  have hH : ∀ x ∈ S, ∀ y, H.Adj x y ↔ (W.append Q).toSubgraph.Adj x y := by
    intro x hx y
    rw [complement_adj_at D.family D.rep.index A hx,D.rep.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    have hn : ¬D.rep.cycle.toSubgraph.Adj x y := fun hh ↦
      Set.disjoint_left.mp hcycle (D.rep.cycle.toSubgraph.edge_vert hh) hx
    rw [or_iff_right hn,hform]
  have he := prefix_run_graph_form W Q S hr hw H hP hH
  let J := H₀ ⊔ chords (runs W S) (runStart W) (runFinish W)
  have hJ : J.support ⊆ Sᶜ := by
    rintro x ⟨y,hxy|hxy⟩
    · exact within_support H Sᶜ ⟨y,hxy⟩
    · exact run_chords_outside W S ⟨y,hxy⟩
  have hJc : SupportConnected J := by
    intro x hx y hy
    exact (hc x (hcore.symm ▸ hJ hx) y (hcore.symm ▸ hJ hy)).mono le_sup_left
  have hwJ : w ∈ J.support := SimpleGraph.support_mono le_sup_left (hcore.symm ▸ hw)
  have hQ : ∀ z ∈ Q.support, z ≠ w → z ∈ S := by
    intro z hz hzw
    by_contra hzS
    exact hzw (hQlast z hz hzS)
  obtain ⟨E,hE,hEc⟩ := marked_prefix_run_partition F.smaller W Q hp S hw hfinish hQ H₀
    (within_support H Sᶜ)
    (prefix_tail_runs_fresh D.family D.score D.root D.rep
      (fun U M hs _ hMC ↦ D.tail_minimum U M hs hMC) A S (fun _ h ↦ h) W Q hform)
    hJc hwJ hhalf
  obtain ⟨E',hE',hE'c⟩ := partition_transport he.symm ⟨E,hE,hEc⟩
  have hpaths (j) (hj : j ∉ Finset.univ \ B) : (D.family.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (D.family.one_defect_other_paths D.score D.rep.index D.rep.member_not_path).2 j
      ((mem_componentMembers D.family D.rep.index j A).mp hjB).1
  obtain ⟨E'',hE'',hE''c⟩ := replace_selected D.family (Finset.univ \ B) hpaths E' hE'
  have hcard : (Finset.univ \ B).card=budget F.order-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ budget F.order := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply F.failure
  refine ⟨E'',hE'',?_⟩
  rw [hcard] at hE''c
  change B.card+⌈(Sᶜ.ncard : ℚ)/2⌉₊ ≤ _ at hbudget
  omega

end Erdos583MarkedTailSuppressionDevelopment
