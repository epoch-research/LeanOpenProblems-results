import Submission.Work

/-! Graph-level restrictions on edge-minimal path-decomposition failures.
These restrictions do not exclude all failures. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
namespace Erdos583NonbridgeCoreDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma repeated_first_edge_not_bridge {V : Type*} {G : SimpleGraph V} {r x b : V}
    (h : G.Adj r x) (p : G.Walk x b) (hp : (Walk.cons h p).IsTrail)
    (hv : r ∈ p.support) : ¬G.IsBridge s(r,x) := by
  classical
  intro hb
  have he := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hb).2 (p.takeUntil r hv).reverse
  rw [Walk.edges_reverse,List.mem_reverse] at he
  exact (Walk.isTrail_cons h p).mp hp |>.2 (p.edges_takeUntil_subset hv he)

lemma exposed_edge_not_bridge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r x : V} {A : Finset (Fin k)} {B : Finset V}
    (he : ExposedRoot T r A B x) : ¬G.IsBridge s(r,x) := by
  obtain ⟨U,_,_,R,_,ρ,hρ,hx⟩ := he
  obtain ⟨i,b,h,p,_,_,hp,_,hv⟩ := rooted_exposed_rep R ρ hρ hx
  exact repeated_first_edge_not_bridge h p hp hv

/-- The two zero-quota neighbors exposed at a rooted maximum are joined to
the root by nonbridges, not merely arbitrary ambient edges. -/
lemma two_zero_nonbridge_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hr : HasRoot T r) :
    ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧ T.quota x=0 ∧ T.quota y=0 ∧
      ¬G.IsBridge s(r,x) ∧ ¬G.IsBridge s(r,y) := by
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  obtain ⟨B,_,x,y,hxy,hrx,hry,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hn
  exact ⟨x,y,hxy,hrx,hry,RootEnergy.exposed_quota_zero hEx hs hm hxB,
    RootEnergy.exposed_quota_zero hEy hs hm hyB,exposed_edge_not_bridge hEx,exposed_edge_not_bridge hEy⟩

lemma two_even_nonbridge_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hmin : EdgeCritical.EdgeMinimal G k) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (hnb : ¬G.IsBridge s(v,u)) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧
      Even (Nat.card (G.neighborSet x)) ∧ Even (Nat.card (G.neighborSet y)) ∧
      ¬G.IsBridge s(v,x) ∧ ¬G.IsBridge s(v,y) := by
  obtain ⟨T,hs,hr,hm⟩ := hmin.root_at_other_endpoint hG hfail h hu hnb
  obtain ⟨x,y,hxy,hvx,hvy,hx,hy,hnbx,hnby⟩ := two_zero_nonbridge_neighbors T v hs hm hr
  exact ⟨x,y,hxy,hvx,hvy,QuotaParity.zero_quota_even T hx,
    QuotaParity.zero_quota_even T hy,hnbx,hnby⟩

/-- A nonbridge endpoint has a second, distinct nonbridge neighbor. -/
lemma nonbridge_has_other_neighbor {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj v u) (hnb : ¬G.IsBridge s(v,u)) :
    ∃ w, w ≠ u ∧ G.Adj v w ∧ ¬G.IsBridge s(v,w) := by
  classical
  have hex : ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ s(v,u) ∈ p.edges := by
    by_contra! hn
    exact hnb (isBridge_iff_adj_and_forall_cycle_notMem.mpr ⟨h,fun _ p hp ↦ hn _ p hp⟩)
  obtain ⟨a,p,hp,he⟩ := hex
  have hv := p.fst_mem_support_of_mem_edges he
  have hc := hp.ncard_neighborSet_toSubgraph_eq_two hv
  obtain ⟨x,y,hxy,hset⟩ := Set.ncard_eq_two.mp hc
  have hedge (w : V) (hw : w ∈ ({x,y} : Set V)) : G.Adj v w ∧ ¬G.IsBridge s(v,w) := by
    have hw' : p.toSubgraph.Adj v w := by
      change w ∈ p.toSubgraph.neighborSet v
      rwa [hset]
    refine ⟨p.toSubgraph.adj_sub hw',?_⟩
    intro hb
    exact (isBridge_iff_adj_and_forall_cycle_notMem.mp hb).2 p hp
      (p.mem_edges_toSubgraph.mp (show s(v,w) ∈ p.toSubgraph.edgeSet from hw'))
  by_cases hx : x=u
  · obtain ⟨hy,hyb⟩ := hedge y (by simp)
    exact ⟨y,fun hh ↦ hxy (hx.trans hh.symm),hy,hyb⟩
  · obtain ⟨hx',hxb⟩ := hedge x (by simp)
    exact ⟨x,hx,hx',hxb⟩

/-- Retain precisely the nonbridge edges with at least one even-degree
endpoint. Parity is always measured in G, not in the retained graph. -/
def evenNonbridgeCore {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬G.IsBridge s(a,b) ∧
    (Even (Nat.card (G.neighborSet a)) ∨ Even (Nat.card (G.neighborSet b)))
  symm a b h := ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2.1,h.2.2.symm⟩
  loopless a h := G.loopless a h.1

lemma evenNonbridgeCore_le {V : Type*} (G : SimpleGraph V) : evenNonbridgeCore G ≤ G :=
  fun _ _ h ↦ h.1

lemma core_no_dead_end {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hmin : EdgeCritical.EdgeMinimal G k) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    {a b : V} (hab : (evenNonbridgeCore G).Adj a b) :
    ∃ c, (evenNonbridgeCore G).Adj b c ∧ c ≠ a := by
  have hba : G.Adj b a := hab.1.symm
  have hnb : ¬G.IsBridge s(b,a) := by simpa only [Sym2.eq_swap] using hab.2.1
  by_cases hb : Even (Nat.card (G.neighborSet b))
  · obtain ⟨c,hca,hbc,hnbc⟩ := nonbridge_has_other_neighbor hba hnb
    exact ⟨c,⟨hbc,hnbc,Or.inl hb⟩,hca⟩
  · have ha : Even (Nat.card (G.neighborSet a)) := hab.2.2.resolve_right hb
    obtain ⟨x,y,hxy,hbx,hby,hx,hy,hnbx,hnby⟩ :=
      two_even_nonbridge_neighbors hmin hG hfail hba ha hnb
    by_cases hxa : x=a
    · exact ⟨y,⟨hby,hnby,Or.inr hy⟩,fun hya ↦ hxy (hxa.trans hya.symm)⟩
    · exact ⟨x,⟨hbx,hnbx,Or.inr hx⟩,hxa⟩

lemma core_not_acyclic {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hmin : EdgeCritical.EdgeMinimal G ⌈(Fintype.card V : ℚ)/2⌉₊) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) : ¬(evenNonbridgeCore G).IsAcyclic := by
  obtain ⟨u,v,h,hu,hnb⟩ := EdgeDefect.failure_has_even_nonbridge G hfail
  apply TokenObstruction.cycle_of_no_dead_end (evenNonbridgeCore G) ⟨v,u,h,hnb,Or.inr hu⟩
  exact core_no_dead_end hmin hG hfail

/-- A critical failure has a cycle in which odd-degree vertices are never
consecutive. Every edge of this cycle is a nonbridge in G. -/
lemma exists_cycle_no_consecutive_odd {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hmin : EdgeCritical.EdgeMinimal G ⌈(Fintype.card V : ℚ)/2⌉₊) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ {u v}, s(u,v) ∈ p.edges →
      ¬G.IsBridge s(u,v) ∧
      (Even (Nat.card (G.neighborSet u)) ∨ Even (Nat.card (G.neighborSet v))) := by
  have hc := core_not_acyclic hmin hG hfail
  simp only [SimpleGraph.IsAcyclic,not_forall,not_not] at hc
  obtain ⟨a,p,hp⟩ := hc
  refine ⟨a,p.mapLe (evenNonbridgeCore_le G),hp.mapLe _,?_⟩
  intro u v he
  have he' : s(u,v) ∈ p.edges := by simpa [Walk.mapLe] using he
  exact (p.adj_of_mem_edges he').2

/-- If the critical graph additionally has an acyclic even-induced graph,
the core has no even-even edges. This does not assert that taking a critical
spanning subgraph preserves the extra acyclicity hypothesis. -/
lemma core_endpoints_opposite_of_even_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hmin : EdgeCritical.EdgeMinimal G k) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (hf : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic)
    {u v : V} (h : (evenNonbridgeCore G).Adj u v) :
    Even (Nat.card (G.neighborSet u)) ↔ Odd (Nat.card (G.neighborSet v)) := by
  rw [←Nat.not_even_iff_odd]
  constructor
  · intro hu hv
    exact h.2.1 (hmin.even_even_edge_isBridge_of_even_forest hG hfail hf h.1 hv hu)
  · intro hv
    exact h.2.2.resolve_right hv

/-- Every connected counterexample has a connected critical spanning
counterexample whose nonbridge even-incident core contains a cycle. -/
lemma failure_has_critical_core_cycle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) ∧
      EdgeCritical.EdgeMinimal H ⌈(Fintype.card V : ℚ)/2⌉₊ ∧
      ¬(evenNonbridgeCore H).IsAcyclic := by
  obtain ⟨H,hHG,hH,hfailH,hmin⟩ := EdgeCritical.exists_edge_minimal_failure G hG _ hfail
  exact ⟨H,hHG,hH,hfailH,hmin,core_not_acyclic hmin hH hfailH⟩

end Erdos583NonbridgeCoreDevelopment
