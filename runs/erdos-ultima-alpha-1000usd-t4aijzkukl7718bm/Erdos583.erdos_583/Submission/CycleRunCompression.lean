import Submission.CycleRunIntervals

/-! Compression of all maximal cycle runs with private interiors. The freshness
of shortcuts in the non-cycle remainder is an explicit hypothesis. -/
namespace Erdos583CycleRunCompressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PrivatePathExpansionDevelopment
open Erdos583PathIntervalsDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {r : V}

omit [Fintype V] in
lemma cycle_run_graph_form (C : G.Walk r r) (S : Set V) (hr : r ∉ S)
    (F : SimpleGraph V) (hCF : C.toSubgraph.spanningCoe ≤ F)
    (hF : ∀ x ∈ S, ∀ y, F.Adj x y ↔ C.toSubgraph.Adj x y) :
    F=within F Sᶜ ⊔ arcs (runs C S) (runPath C) := by
  ext x y
  constructor
  · intro hxy
    by_cases hx : x ∈ S
    · obtain ⟨p,hp,hxyP⟩ := runs_cover_inside_edges C S hr ((hF x hx y).mp hxy) (Or.inl hx)
      exact Or.inr ((arcs_adj _ _ _ _).mpr ⟨p,hp,hxyP⟩)
    · by_cases hy : y ∈ S
      · obtain ⟨p,hp,hyxP⟩ := runs_cover_inside_edges C S hr ((hF y hy x).mp hxy.symm) (Or.inl hy)
        exact Or.inr ((arcs_adj _ _ _ _).mpr ⟨p,hp,hyxP.symm⟩)
      · exact Or.inl ⟨hxy,hx,hy⟩
  · rintro (hxy|hxy)
    · exact hxy.1
    · obtain ⟨p,_,hxy⟩ := (arcs_adj _ _ _ _).mp hxy
      exact hCF (show C.toSubgraph.Adj x y from runPath_edges_subset C p (show s(x,y) ∈ (runPath C p).toSubgraph.edgeSet from hxy))

lemma cycle_run_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (C : G.Walk r r) (hc : C.IsCycle) (S : Set V) (hr : r ∉ S)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < C.length)
    (ht : C.getVert t ∉ S) (hu : C.getVert u ∉ S)
    (F : SimpleGraph V) (hCF : C.toSubgraph.spanningCoe ≤ F)
    (hF : ∀ x ∈ S, ∀ y, F.Adj x y ↔ C.toSubgraph.Adj x y)
    (hfresh : ∀ p ∈ runs C S, ¬(within F Sᶜ).Adj (runStart C p) (runFinish C p))
    (hFc : SupportConnected F) (hsize : Sᶜ.ncard < n) :
    ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
  let A := runs C S
  let a := runStart C
  let b := runFinish C
  let P := runPath C
  let H := within F Sᶜ
  have hrun (p : RunIndex C) (hp : p ∈ A) := (mem_runs C S p).mp hp
  have hab (p : RunIndex C) (hp : p ∈ A) : a p ≠ b p :=
    (hrun p hp).endpoint_ne C hc S ht0 (by omega) ht
  have hp (p : RunIndex C) (hp : p ∈ A) : (P p).IsPath :=
    cycle_interval_path C hc (by have := p.property; omega) (hrun p hp).2.1 (hab p hp)
  have hprivate (p : RunIndex C) (hp : p ∈ A) (q : RunIndex C) (hq : q ∈ A) (hpq : p ≠ q)
      (z : V) (hz : z ∈ (P p).support) (hza : z ≠ a p) (hzb : z ≠ b p) : z ∉ (P q).support := by
    apply (hrun p hp).private C hc S hr (hrun q hq) _ hz hza hzb
    rintro ⟨h1,h2⟩
    exact hpq (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
  have hinj (p : RunIndex C) (hp : p ∈ A) (q : RunIndex C) (hq : q ∈ A)
      (he : s(a p,b p)=s(a q,b q)) : p=q := by
    obtain ⟨h1,h2⟩ := (hrun p hp).shortcuts_injective C hc S ht0 htu huN ht hu (hrun q hq) he
    exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
  have hnoarc (p : RunIndex C) (hp : p ∈ A) (q : RunIndex C) (_hq : q ∈ A) :
      s(a p,b p) ∉ (P q).edges := by
    intro he
    apply (hrun p hp).shortcut_not_cycle_edge C hc S ht0 htu huN ht hu
    exact C.mem_edges_toSubgraph.mp (runPath_edges_subset C q ((P q).mem_edges_toSubgraph.mpr he))
  have hform := cycle_run_graph_form C S hr F hCF hF
  obtain ⟨D,hD,hDc⟩ := compressed_private_partition hsmall A a b P H S hp
    (fun p hp ↦ (hrun p hp).2.2.1) (fun p hp ↦ (hrun p hp).2.2.2.1) hab
    (within_support F Sᶜ) (fun p hp _ hz hza hzb ↦ (hrun p hp).internal_mem C S hz hza hzb)
    hprivate hfresh hinj hnoarc (hform ▸ hFc) hsize
  exact Eq.mp (congrArg (fun J : SimpleGraph V ↦ ∃ E : Finset J.Subgraph,
    GoodDecomposition J E ∧ E.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊) hform.symm) ⟨D,hD,hDc⟩

end Erdos583CycleRunCompressionDevelopment
