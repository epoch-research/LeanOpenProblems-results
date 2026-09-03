import Submission.Work

/-! Contracting a nonempty vertex set to a star, retaining its exterior edges. -/
namespace Erdos583StarContractionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} (G : SimpleGraph V) (S : Set V) (r : V) (hr : r ∈ S)

def contract : SimpleGraph V where
  Adj x y := (G.Adj x y ∧ x ∉ S ∧ y ∉ S) ∨
    (x=r ∧ y ∉ S ∧ ∃ z ∈ S, G.Adj z y) ∨ (y=r ∧ x ∉ S ∧ ∃ z ∈ S, G.Adj z x)
  symm := by
    intro x y h
    rcases h with ⟨hxy,hx,hy⟩|h|h
    · exact Or.inl ⟨hxy.symm,hy,hx⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    intro x h
    rcases h with ⟨hxx,_,_⟩|⟨hxr,hx,_⟩|⟨hxr,hx,_⟩
    · exact G.loopless x hxx
    all_goals exact hx (hxr.symm ▸ hr)

lemma adj_outside {x y : V} (hx : x ∉ S) (hy : y ∉ S) :
    (contract G S r hr).Adj x y ↔ G.Adj x y := by
  constructor
  · rintro (h|h|h)
    · exact h.1
    · exact (hx (h.1.symm ▸ hr)).elim
    · exact (hy (h.1.symm ▸ hr)).elim
  · intro h
    exact Or.inl ⟨h,hx,hy⟩

lemma adj_center {y : V} : (contract G S r hr).Adj r y ↔
    y ∉ S ∧ ∃ z ∈ S, G.Adj z y := by
  constructor
  · rintro (h|h|h)
    · exact (h.2.1 hr).elim
    · exact h.2
    · exact (h.2.1 hr).elim
  · intro h
    exact Or.inr (Or.inl ⟨rfl,h⟩)

lemma adj_left {x y : V} (h : (contract G S r hr).Adj x y) : x ∈ Sᶜ ∪ {r} := by
  rcases h with h|h|h
  · exact Or.inl h.2.1
  · exact Or.inr h.1
  · exact Or.inl h.2.1

lemma within_eq : within (contract G S r hr) (Sᶜ ∪ {r})=contract G S r hr := by
  ext x y
  exact ⟨And.left,fun h ↦ ⟨h,adj_left G S r hr h,adj_left G S r hr h.symm⟩⟩

noncomputable def collapse (x : V) : V := if x ∈ S then r else x

lemma collapse_mem (x : V) : collapse S r x ∈ Sᶜ ∪ {r} := by
  by_cases hx : x ∈ S <;> simp [collapse,hx]

lemma collapse_adj_reachable {x y : V} (h : G.Adj x y) :
    (contract G S r hr).Reachable (collapse S r x) (collapse S r y) := by
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [collapse,if_pos hx,if_pos hy]
    exact .rfl
  · simp only [collapse,if_pos hx,if_neg hy]
    exact (adj_center G S r hr |>.mpr ⟨hy,x,hx,h⟩).reachable
  · simp only [collapse,if_neg hx,if_pos hy]
    exact (adj_center G S r hr |>.mpr ⟨hx,y,hy,h.symm⟩).reachable.symm
  · simp only [collapse,if_neg hx,if_neg hy]
    exact (adj_outside G S r hr hx hy |>.mpr h).reachable

lemma collapse_walk {x y : V} (P : G.Walk x y) :
    (contract G S r hr).Reachable (collapse S r x) (collapse S r y) := by
  induction P with
  | nil => exact .rfl
  | cons h P ih => exact (collapse_adj_reachable G S r hr h).trans ih

lemma connected_induce (hG : G.Connected) :
    ((contract G S r hr).induce (Sᶜ ∪ {r})).Connected := by
  have hc (x : (Sᶜ ∪ {r} : Set V)) : collapse S r x.val=x.val := by
    rcases x.property with hx|hx
    · simp only [collapse,if_neg hx]
    · change x.val=r at hx
      simp only [collapse,hx,if_pos hr]
  have hreach (x y : (Sᶜ ∪ {r} : Set V)) : (contract G S r hr).Reachable x.val y.val := by
    obtain ⟨P⟩ := hG x.val y.val
    simpa only [hc x,hc y] using collapse_walk G S r hr P
  letI : Nonempty (Sᶜ ∪ {r} : Set V) := ⟨⟨r,Or.inr rfl⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨P⟩ := hreach x y
  have hv : ∀ z ∈ P.support, z ∈ Sᶜ ∪ {r} := by
    intro z hz
    by_cases hn : P.Nil
    · have hz' : z=x.val := by
        have hh := Walk.nil_iff_support_eq.mp hn
        simpa only [hh,List.mem_singleton] using hz
      exact hz' ▸ x.property
    · obtain ⟨w,hw⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor P hn (P.mem_verts_toSubgraph.mpr hz)
      exact adj_left G S r hr (P.toSubgraph.adj_sub hw)
  exact ⟨(P.induce _ hv).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

include hr in
lemma card_vertices [Fintype V] :
    (Sᶜ ∪ {r}).ncard+S.ncard=Fintype.card V+1 := by
  have hd : Disjoint Sᶜ ({r} : Set V) := Set.disjoint_singleton_right.mpr (by simpa only [Set.mem_compl_iff,not_not] using hr)
  rw [Set.ncard_union_eq hd,Set.ncard_singleton]
  have hh := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hh
  omega

lemma exterior_edge {x y : V} (h : (contract G S r hr).Adj x y) (hx : x ≠ r) (hy : y ≠ r) :
    G.Adj x y ∧ x ∉ S ∧ y ∉ S := by
  rcases h with h|h|h
  · exact h
  · exact (hx h.1).elim
  · exact (hy h.1).elim

lemma transfer_edges {a b : V} (P : (contract G S r hr).Walk a b) (hP : r ∉ P.support) :
    ∀ e ∈ P.edges, e ∈ G.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    have hxy := P.mem_edges_toSubgraph.mpr he
    have hx : x ≠ r := fun h ↦ hP (h ▸ Walk.mem_support_of_adj_toSubgraph hxy)
    have hy : y ≠ r := fun h ↦ hP (h ▸ Walk.mem_support_of_adj_toSubgraph hxy.symm)
    exact (exterior_edge G S r hr (P.toSubgraph.adj_sub hxy) hx hy).1

noncomputable def lift {a b : V} (P : (contract G S r hr).Walk a b) (hP : r ∉ P.support) :
    G.Walk a b := P.transfer G (transfer_edges G S r hr P hP)

lemma lift_support {a b : V} (P : (contract G S r hr).Walk a b) (hP : r ∉ P.support) :
    (lift G S r hr P hP).support=P.support := Walk.support_transfer _ _

lemma lift_edges {a b : V} (P : (contract G S r hr).Walk a b) (hP : r ∉ P.support) :
    (lift G S r hr P hP).toSubgraph.edgeSet=P.toSubgraph.edgeSet := by
  ext e
  simp only [Walk.mem_edges_toSubgraph,lift,Walk.edges_transfer]

lemma lift_isPath {a b : V} (P : (contract G S r hr).Walk a b) (hP : r ∉ P.support) (hp : P.IsPath) :
    (lift G S r hr P hP).IsPath := by
  rw [Walk.isPath_def,lift_support]
  exact hp.support_nodup

lemma support_outside {a b : V} (P : (contract G S r hr).Walk a b) (hP : r ∉ P.support)
    (ha : a ∉ S) : ∀ x ∈ P.support, x ∉ S := by
  intro x hx
  by_cases hn : P.Nil
  · have he : x=a := by
      have hh := Walk.nil_iff_support_eq.mp hn
      simpa only [hh,List.mem_singleton] using hx
    exact he ▸ ha
  · obtain ⟨y,hxy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor P hn (P.mem_verts_toSubgraph.mpr hx)
    rcases adj_left G S r hr (P.toSubgraph.adj_sub hxy) with hx|hx
    · exact hx
    · exact (hP (hx ▸ (Walk.mem_support_of_adj_toSubgraph hxy))).elim

end Erdos583StarContractionDevelopment
