import Submission.TailRunFreshness

/-! A common interface for compressing cycle and path runs. The deleted
interior set is the intersection of the ambient deletion set with the walk. -/
namespace Erdos583RunCompressionDataDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583CycleRunIntervalsDevelopment Erdos583PathRunIntervalsDevelopment
open Erdos583PathIntervalsDevelopment Erdos583PrivatePathExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable {V : Type*} {G : SimpleGraph V} {a b : V}

lemma run_support_subset (W : G.Walk a b) (p : RunIndex W) :
    (runPath W p).support ⊆ W.support := by
  intro z hz
  obtain ⟨m,_,_,rfl⟩ := (interval_support W (by have := p.property; omega)
    (by have := p.val.2.isLt; omega) z).mp hz
  exact W.getVert_mem_support m

lemma run_arcs_support (W : G.Walk a b) (S : Set V) :
    (arcs (runs W S) (runPath W)).support ⊆ W.toSubgraph.verts := by
  rintro x ⟨y,hxy⟩
  obtain ⟨p,_,hxy⟩ := (arcs_adj _ _ _ _).mp hxy
  exact W.mem_verts_toSubgraph.mpr (run_support_subset W p (Walk.mem_support_of_adj_toSubgraph hxy))

lemma run_chords_support (W : G.Walk a b) (S : Set V) :
    (chords (runs W S) (runStart W) (runFinish W)).support ⊆ W.toSubgraph.verts := by
  rintro x ⟨y,hxy⟩
  obtain ⟨p,_,hxy⟩ := (chords_adj _ _ _ _ _).mp hxy
  rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨rfl,_⟩|⟨rfl,_⟩,_⟩ <;>
    exact W.mem_verts_toSubgraph.mpr (W.getVert_mem_support _)

lemma run_chords_outside (W : G.Walk a b) (S : Set V) :
    (chords (runs W S) (runStart W) (runFinish W)).support ⊆ Sᶜ :=
  chords_support_outside _ _ _ _ (fun p hp ↦ ((mem_runs W S p).mp hp).2.2.1)
    (fun p hp ↦ ((mem_runs W S p).mp hp).2.2.2.1)

structure RunConditions (W : G.Walk a b) (S : Set V) : Prop where
  path : ∀ p ∈ runs W S, (runPath W p).IsPath
  ne : ∀ p ∈ runs W S, runStart W p ≠ runFinish W p
  privacy : ∀ p ∈ runs W S, ∀ q ∈ runs W S, p ≠ q → ∀ z ∈ (runPath W p).support,
    z ≠ runStart W p → z ≠ runFinish W p → z ∉ (runPath W q).support
  injective : ∀ p ∈ runs W S, ∀ q ∈ runs W S,
    s(runStart W p,runFinish W p)=s(runStart W q,runFinish W q) → p=q
  no_edge : ∀ p ∈ runs W S, s(runStart W p,runFinish W p) ∉ W.edges

lemma cycle_run_conditions {r : V} (C : G.Walk r r) (hc : C.IsCycle) (S : Set V) (hr : r ∉ S)
    {t u : ℕ} (ht0 : 0 < t) (htu : t < u) (huN : u < C.length)
    (ht : C.getVert t ∉ S) (hu : C.getVert u ∉ S) : RunConditions C S := by
  have hrun (p : RunIndex C) (hp : p ∈ runs C S) := (mem_runs C S p).mp hp
  have hab (p : RunIndex C) (hp : p ∈ runs C S) : runStart C p ≠ runFinish C p :=
    (hrun p hp).endpoint_ne C hc S ht0 (by omega) ht
  refine ⟨?_,hab,?_,?_,?_⟩
  · intro p hp
    exact cycle_interval_path C hc (by have := p.property; omega) (hrun p hp).2.1 (hab p hp)
  · intro p hp q hq hpq z hz hza hzb
    apply (hrun p hp).private C hc S hr (hrun q hq) _ hz hza hzb
    rintro ⟨h1,h2⟩
    exact hpq (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
  · intro p hp q hq he
    obtain ⟨h1,h2⟩ := (hrun p hp).shortcuts_injective C hc S ht0 htu huN ht hu (hrun q hq) he
    exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
  · intro p hp
    exact (hrun p hp).shortcut_not_cycle_edge C hc S ht0 htu huN ht hu

lemma path_run_conditions (P : G.Walk a b) (hp : P.IsPath) (S : Set V) : RunConditions P S := by
  have hrun (p : RunIndex P) (hp : p ∈ runs P S) := (mem_runs P S p).mp hp
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p _
    exact interval_isPath P hp _
  · intro p h
    exact run_endpoint_ne P hp S (hrun p h)
  · intro p h q hq hpq z hz hza hzb
    apply run_private P hp S (hrun p h) (hrun q hq) _ hz hza hzb
    rintro ⟨h1,h2⟩
    exact hpq (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
  · intro p h q hq he
    obtain ⟨h1,h2⟩ := run_shortcuts_injective P hp S (hrun p h) (hrun q hq) he
    exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
  · intro p h
    exact run_shortcut_not_path_edge P hp S (hrun p h)

lemma RunConditions.no_arc (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (p : RunIndex W) (hp : p ∈ runs W S) (q : RunIndex W) :
    s(runStart W p,runFinish W p) ∉ (runPath W q).edges := by
  intro he
  exact h.no_edge p hp (W.mem_edges_toSubgraph.mp
    (runPath_edges_subset W q ((runPath W q).mem_edges_toSubgraph.mpr he)))

lemma RunConditions.connected (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (H : SimpleGraph V) (hH : H.support ⊆ (W.toSubgraph.verts ∩ S)ᶜ)
    (hc : SupportConnected (H ⊔ arcs (runs W S) (runPath W))) :
    SupportConnected (H ⊔ chords (runs W S) (runStart W) (runFinish W)) := by
  apply compressed_support_connected _ _ _ _ H (W.toSubgraph.verts ∩ S) _ _ h.ne hH _ h.privacy hc
  · intro p hp hz
    exact ((mem_runs W S p).mp hp).2.2.1 hz.2
  · intro p hp hz
    exact ((mem_runs W S p).mp hp).2.2.2.1 hz.2
  · intro p hp z hz hza hzb
    exact ⟨W.mem_verts_toSubgraph.mpr (run_support_subset W p hz),
      ((mem_runs W S p).mp hp).internal_mem W S hz hza hzb⟩

lemma RunConditions.expand [Fintype V] (W : G.Walk a b) (S : Set V) (h : RunConditions W S)
    (H : SimpleGraph V) (hH : H.support ⊆ (W.toSubgraph.verts ∩ S)ᶜ)
    (hfresh : ∀ p ∈ runs W S, ¬H.Adj (runStart W p) (runFinish W p))
    (D : Finset (H ⊔ chords (runs W S) (runStart W) (runFinish W)).Subgraph)
    (hD : GoodDecomposition _ D) :
    ∃ E : Finset (H ⊔ arcs (runs W S) (runPath W)).Subgraph,
      GoodDecomposition _ E ∧ E.card ≤ D.card := by
  apply expand_private_paths _ _ _ _ H (W.toSubgraph.verts ∩ S) h.path _ _ h.ne hH _
    h.privacy hfresh h.injective (fun p hp q _ ↦ h.no_arc W S p hp q) D hD
  · intro p hp hz
    exact ((mem_runs W S p).mp hp).2.2.1 hz.2
  · intro p hp hz
    exact ((mem_runs W S p).mp hp).2.2.2.1 hz.2
  · intro p hp z hz hza hzb
    exact ⟨W.mem_verts_toSubgraph.mpr (run_support_subset W p hz),
      ((mem_runs W S p).mp hp).internal_mem W S hz hza hzb⟩

end Erdos583RunCompressionDataDevelopment
