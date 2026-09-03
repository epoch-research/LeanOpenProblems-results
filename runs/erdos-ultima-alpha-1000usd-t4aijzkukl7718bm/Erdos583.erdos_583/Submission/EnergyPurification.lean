import Submission.Work

/-! Secondary optimization of purification: a shortest-member obstruction. -/
open SimpleGraph Erdos583Work
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583Work.PendantCompletion Erdos583Work.LeafPermutation
open Erdos583Work.SingletonRotation Erdos583Work.InducedBuffer
open Erdos583Work.VertexTracking Erdos583Work.EnergyTransport
namespace Erdos583EnergyPurificationDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma leafPart_isInduced {V : Type*} (G : SimpleGraph V) (z : V) :
    (leafPart G z).IsInduced := by
  intro x hx y hy hxy
  rw [leafPart_verts] at hx hy
  rcases (show x=Sum.inl z ∨ x=Sum.inr ⟨z,Set.mem_univ _⟩ by simpa using hx) with rfl | rfl <;>
    rcases (show y=Sum.inl z ∨ y=Sum.inr ⟨z,Set.mem_univ _⟩ by simpa using hy) with rfl | rfl
  · exact (hxy.ne rfl).elim
  · change s(Sum.inl z,Sum.inr ⟨z,Set.mem_univ _⟩) ∈ (leafPart G z).edgeSet
    simp [leafPart_edges]
  · change s(Sum.inr ⟨z,Set.mem_univ _⟩,Sum.inl z) ∈ (leafPart G z).edgeSet
    simp [leafPart_edges,Sym2.eq_swap]
  · exact (hxy.ne rfl).elim

lemma leafPart_vertex_rigid {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V ⊕ (Set.univ : Set V)} (p : (allLeafCompletion G).Walk a b) (z : V)
    (he : p.toSubgraph.verts=(leafPart G z).verts) : p.toSubgraph=leafPart G z :=
  induced_path_verts_determine (leafWalk (Walk.nil : G.Walk z z))
    (leafWalk_isPath _ Walk.IsPath.nil) (leafPart_isInduced G z) p he

lemma leafPart_vertex_ncard {V : Type*} (G : SimpleGraph V) (z : V) :
    (leafPart G z).verts.ncard=2 := by
  rw [leafPart_verts,Set.ncard_pair (by simp)]

lemma purified_subset_of_vertex_transfer {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T U : NormalTrailSystem (allLeafCompletion G) k) (i r : Fin k)
    (hi : 3 ≤ (T.walk i).toSubgraph.verts.ncard)
    (hr : 3 ≤ (T.walk r).toSubgraph.verts.ncard)
    (hrest : ∀ l, l ≠ i → l ≠ r → (U.walk l).toSubgraph.verts=(T.walk l).toSubgraph.verts) :
    purified T ⊆ purified U := by
  intro z hz
  obtain ⟨l,hl⟩ := (mem_purified T z).mp hz
  have hli : l ≠ i := by
    rintro rfl
    rw [hl,leafPart_vertex_ncard] at hi
    omega
  have hlr : l ≠ r := by
    rintro rfl
    rw [hl,leafPart_vertex_ncard] at hr
    omega
  apply (mem_purified U z).mpr
  exact ⟨l,leafPart_vertex_rigid (U.walk l) z (by rw [hrest l hli hlr,hl])⟩

lemma member_two_verts_leafPart {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) (r : Fin k) (z : V)
    (hz : Sum.inr ⟨z,Set.mem_univ _⟩ ∈ (T.walk r).toSubgraph.verts)
    (hc : (T.walk r).toSubgraph.verts.ncard ≤ 2) :
    (T.walk r).toSubgraph=leafPart G z := by
  obtain ⟨x,hx⟩ := walk_vertex_has_subgraph_neighbor (T.walk r)
    (Walk.not_nil_of_ne (T.endpoints_ne r)) hz
  have hxu : x=Sum.inl z := (leaf_adj ⟨z,Set.mem_univ _⟩ x).mp ((T.walk r).toSubgraph.adj_sub hx)
  have hu : Sum.inl z ∈ (T.walk r).toSubgraph.verts := hxu ▸ (T.walk r).toSubgraph.edge_vert hx.symm
  apply leafPart_vertex_rigid (T.walk r) z
  symm
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · rw [leafPart_verts]
    intro y hy
    rcases (show y=Sum.inl z ∨ y=Sum.inr ⟨z,Set.mem_univ _⟩ by simpa using hy) with rfl | rfl
    · exact hu
    · exact hz
  · rw [leafPart_vertex_ncard]
    exact hc

/-- In a maximum-purification path system, maximize the secondary energy.
Shortening any smallest non-singleton member must use a two-vertex recipient.
This does not assert that the purified set is large. -/
lemma shortest_member_recipient_two_verts {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath)
    (hmax : ∀ U : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (U.walk l).IsPath) → (purified U).card ≤ (purified T).card)
    (henergy : ∀ U : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (U.walk l).IsPath) → (purified U).card=(purified T).card →
      vertexEnergy U ≤ vertexEnergy T)
    (i j : Fin k) (hij : i ≠ j)
    (hi : 3 ≤ (T.walk i).toSubgraph.verts.ncard)
    (hsmall : ∀ r : Fin k, 3 ≤ (T.walk r).toSubgraph.verts.ncard →
      (T.walk i).toSubgraph.verts.ncard ≤ (T.walk r).toSubgraph.verts.ncard)
    (h : (allLeafCompletion G).Adj (T.start i) (T.start j))
    (p : (allLeafCompletion G).Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hnot : T.start i ∉ p.support)
    (hnadj : ¬(allLeafCompletion G).Adj (T.start i) (T.finish i)) :
    ∃ U : NormalTrailSystem (allLeafCompletion G) k,
      U.score=T.score ∧ (∀ l, (U.walk l).IsPath) ∧
      (U.walk i).toSubgraph=p.toSubgraph ∧
      ∃ r : Fin k, i ≠ r ∧ (T.walk r).toSubgraph.verts.ncard ≤ 2 ∧
        ∃ x ∈ (T.walk r).support, ∃ ha : (allLeafCompletion G).Adj (T.start i) x,
          (U.walk r).toSubgraph=(allLeafCompletion G).subgraphOfAdj ha ⊔ (T.walk r).toSubgraph := by
  obtain ⟨U,hU,hUi,r,hir,hr,hrec,hrest,hE⟩ := shorten_oriented_energy T i j hij h p hp he hnot hnadj
  have hpU : ∀ l, (U.walk l).IsPath := by
    apply U.score_eq_edges_add_iff.mp
    rw [hU,T.score_eq_edges_add_iff.mpr hpT]
  refine ⟨U,hU,hpU,hUi,r,hir,?_,hrec⟩
  by_contra! hr3
  have hsub := purified_subset_of_vertex_transfer T U i r hi hr3 hrest
  have hc : (purified U).card=(purified T).card :=
    Nat.le_antisymm (hmax U hpU) (Finset.card_le_card hsub)
  have hEn := henergy U hpU hc
  have hlen := hsmall r hr3
  omega

/-- Each member carries a pendant leaf. Canonical permutation lifts have this
property, and shortening at a core vertex preserves it. -/
def LeafCovered {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem (allLeafCompletion G) k) : Prop :=
  ∀ i, ∃ z : V, Sum.inr ⟨z,Set.mem_univ _⟩ ∈ (T.walk i).toSubgraph.verts

lemma leafCovered_transfer {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T U : NormalTrailSystem (allLeafCompletion G) k) (hT : LeafCovered T)
    (i r : Fin k) {a : V} (ha : T.start i=Sum.inl a)
    (hi : (T.walk i).toSubgraph.verts=insert (T.start i) (U.walk i).toSubgraph.verts)
    (hr : (T.walk r).toSubgraph.verts ⊆ (U.walk r).toSubgraph.verts)
    (hrest : ∀ l, l ≠ i → l ≠ r → (U.walk l).toSubgraph.verts=(T.walk l).toSubgraph.verts) :
    LeafCovered U := by
  intro l
  obtain ⟨z,hz⟩ := hT l
  refine ⟨z,?_⟩
  by_cases hli : l=i
  · subst l
    rw [hi,ha] at hz
    simpa using hz
  · by_cases hlr : l=r
    · subst l; exact hr hz
    · rw [hrest l hli hlr]; exact hz

/-- A shortest non-singleton member at a constrained energy maximum can only
send its first core edge to a previously purified leaf singleton. The old
purified set is held fixed as a constraint, not assumed to have a large size. -/
lemma shortest_member_purified_recipient {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath) (hleafT : LeafCovered T)
    (henergy : ∀ U : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (U.walk l).IsPath) → LeafCovered U → purified T ⊆ purified U →
      vertexEnergy U ≤ vertexEnergy T)
    (i j : Fin k) (hij : i ≠ j) {a : V} (ha : T.start i=Sum.inl a)
    (hi : 3 ≤ (T.walk i).toSubgraph.verts.ncard)
    (hsmall : ∀ r : Fin k, 3 ≤ (T.walk r).toSubgraph.verts.ncard →
      (T.walk i).toSubgraph.verts.ncard ≤ (T.walk r).toSubgraph.verts.ncard)
    (h : (allLeafCompletion G).Adj (T.start i) (T.start j))
    (p : (allLeafCompletion G).Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hnot : T.start i ∉ p.support)
    (hnadj : ¬(allLeafCompletion G).Adj (T.start i) (T.finish i)) :
    ∃ U : NormalTrailSystem (allLeafCompletion G) k,
      U.score=T.score ∧ (∀ l, (U.walk l).IsPath) ∧ LeafCovered U ∧
      (U.walk i).toSubgraph=p.toSubgraph ∧
      ∃ r : Fin k, i ≠ r ∧ ∃ z ∈ purified T,
        (T.walk r).toSubgraph=leafPart G z ∧ G.Adj a z := by
  obtain ⟨U,hU,hUi,r,hir,hr,hrec,hrest,hE⟩ := shorten_oriented_energy T i j hij h p hp he hnot hnadj
  have hpU : ∀ l, (U.walk l).IsPath := by
    apply U.score_eq_edges_add_iff.mp
    rw [hU,T.score_eq_edges_add_iff.mpr hpT]
  have hleafU : LeafCovered U := by
    apply leafCovered_transfer T U hleafT i r ha
      (by rw [he,hUi,cons_verts]) _ hrest
    obtain ⟨x,_,hh,hUr⟩ := hrec
    rw [hUr,Subgraph.verts_sup]
    exact Set.subset_union_right
  have hr2 : (T.walk r).toSubgraph.verts.ncard ≤ 2 := by
    by_contra! hr3
    have hsub := purified_subset_of_vertex_transfer T U i r hi hr3 hrest
    have hEn := henergy U hpU hleafU hsub
    have hlen := hsmall r hr3
    omega
  obtain ⟨z,hz⟩ := hleafT r
  have hrL := member_two_verts_leafPart T r z hz hr2
  refine ⟨U,hU,hpU,hleafU,hUi,r,hir,z,(mem_purified T z).mpr ⟨r,hrL⟩,hrL,?_⟩
  obtain ⟨x,hx,hax,_⟩ := hrec
  have hx' : x=Sum.inl z ∨ x=Sum.inr ⟨z,Set.mem_univ _⟩ := by
    rw [← Walk.mem_verts_toSubgraph,hrL,leafPart_verts] at hx
    simpa using hx
  rcases hx' with rfl | rfl
  · rw [ha] at hax
    exact hax
  · have heaz : T.start i=Sum.inl z := (leaf_adj ⟨z,Set.mem_univ _⟩ _).mp hax.symm
    apply (hr ?_).elim
    rw [← Walk.mem_verts_toSubgraph,hrL,heaz,leafPart_verts]
    simp

/-- The constrained energy optimum used above exists: retain the old purified
set and the leaf-covered path property, and maximize a bounded natural weight. -/
lemma exists_constrained_energy_maximum {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : NormalTrailSystem (allLeafCompletion G) k)
    (hpT : ∀ l, (T.walk l).IsPath) (hleafT : LeafCovered T) :
    ∃ U : NormalTrailSystem (allLeafCompletion G) k,
      (∀ l, (U.walk l).IsPath) ∧ LeafCovered U ∧ purified T ⊆ purified U ∧
      ∀ R : NormalTrailSystem (allLeafCompletion G) k,
        (∀ l, (R.walk l).IsPath) → LeafCovered R → purified U ⊆ purified R →
        vertexEnergy R ≤ vertexEnergy U := by
  classical
  let P (m : ℕ) := ∃ U : NormalTrailSystem (allLeafCompletion G) k,
    (∀ l, (U.walk l).IsPath) ∧ LeafCovered U ∧ purified T ⊆ purified U ∧ vertexEnergy U=m
  obtain ⟨U,hpU,hleafU,hsub,hU⟩ := Nat.findGreatest_spec (P := P) (vertexEnergy_le T)
    ⟨T,hpT,hleafT,Finset.Subset.refl _,rfl⟩
  refine ⟨U,hpU,hleafU,hsub,?_⟩
  intro R hpR hleafR hsubR
  rw [hU]
  exact Nat.le_findGreatest (vertexEnergy_le R) ⟨R,hpR,hleafR,Finset.Subset.trans hsub hsubR,rfl⟩

lemma exists_smallest_nonsingleton_member {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hn : ∃ i, 3 ≤ (T.walk i).toSubgraph.verts.ncard) :
    ∃ i : Fin k, 3 ≤ (T.walk i).toSubgraph.verts.ncard ∧
      ∀ r : Fin k, 3 ≤ (T.walk r).toSubgraph.verts.ncard →
        (T.walk i).toSubgraph.verts.ncard ≤ (T.walk r).toSubgraph.verts.ncard := by
  classical
  let L := Finset.univ.filter (fun i ↦ 3 ≤ (T.walk i).toSubgraph.verts.ncard)
  have hL : L.Nonempty := by
    obtain ⟨i,hi⟩ := hn
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨i,hi,hm⟩ := L.exists_min_image (fun i ↦ (T.walk i).toSubgraph.verts.ncard) hL
  exact ⟨i,(Finset.mem_filter.mp hi).2,fun r hr ↦ hm r (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)⟩

end Erdos583EnergyPurificationDevelopment
