import Submission.Work

/-! Global edge minimality at the smallest failing order.
Unlike spanning edge minimality, this permits comparisons with other graphs
of the same order, such as a doubled bridge side. -/
namespace Erdos583GlobalCriticalDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue Erdos583Work.MarkedDouble
open scoped Classical
set_option maxHeartbeats 1600000

/-- Every connected graph of the same order with fewer edges meets the budget.
There is no spanning-subgraph hypothesis. -/
def MinimalEdges {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ H : SimpleGraph (Fin n), H.Connected → H.edgeSet.ncard < G.edgeSet.ncard →
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k

lemma MinimalEdges.spanning {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hmin : MinimalEdges G k) : EdgeCritical.EdgeMinimal G k :=
  fun H _ hH hlt ↦ hmin H hH hlt

lemma exists_minimal_edges {n k : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k) :
    ∃ H : SimpleGraph (Fin n), H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k) ∧
      MinimalEdges H k := by
  classical
  let P (m : ℕ) := ∃ H : SimpleGraph (Fin n), H.Connected ∧
    (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k) ∧ H.edgeSet.ncard=m
  have hex : ∃ m, P m := ⟨G.edgeSet.ncard,G,hG,hfail,rfl⟩
  obtain ⟨H,hH,hfailH,hE⟩ := Nat.find_spec hex
  refine ⟨H,hH,hfailH,?_⟩
  intro J hJ hlt
  by_contra hf
  have hh := Nat.find_min' hex (show P J.edgeSet.ncard from ⟨J,hJ,hf,rfl⟩)
  omega

lemma edge_ncard_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.edgeSet.ncard=H.edgeSet.ncard := by
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
  exact Nat.card_congr e.mapEdgeSet

lemma MinimalEdges.on_finite {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hmin : MinimalEdges G k) {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hsize : Fintype.card V=n) (hH : H.Connected) (hE : H.edgeSet.ncard<G.edgeSet.ncard) :
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k := by
  classical
  let e : Fin n ≃ V := Fintype.equivOfCardEq (by simpa using hsize.symm)
  have hc := edge_ncard_iso (Iso.comap e H)
  change (H.comap e).edgeSet.ncard=H.edgeSet.ncard at hc
  obtain ⟨D,hD,hDc⟩ := hmin (H.comap e) ((Iso.comap e H).connected_iff.mpr hH)
    (by rwa [hc])
  obtain ⟨E,hE,hEc⟩ := hD.map_comap_equiv e
  exact ⟨E,hE,hEc.trans hDc⟩

lemma failure_has_global_minimal_root {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    ∃ H : SimpleGraph (Fin n), H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) ∧
      MinimalEdges H ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ ∧
      EdgeCritical.EdgeMinimal H ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ ∧
      ∃ r : Fin n, ∃ T : QuotaTrails.TrailFamily H ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
        T.score+1=H.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ ∧ QuotaRooted.HasRoot T r ∧
        ∀ U : QuotaTrails.TrailFamily H ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score := by
  obtain ⟨H,hH,hf,hm⟩ := exists_minimal_edges G hG hfail
  obtain ⟨u,v,h,hu,hnb⟩ := EdgeDefect.failure_has_even_nonbridge H hf
  obtain ⟨T,hs,hr,hmax⟩ := hm.spanning.root_at_other_endpoint hH hf h hu hnb
  exact ⟨H,hH,hf,hm,hm.spanning,v,T,hs,hr,hmax⟩

lemma sum_neighbor_ncard {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∑ v, Nat.card (G.neighborSet v)=2*G.edgeSet.ncard := by
  classical
  simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,
    Set.ncard_eq_toFinset_card',edgeFinset] using G.sum_degrees_eq_twice_card_edges

lemma pairedCopies_edge_ncard {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    (pairedCopies G S).edgeSet.ncard=2*G.edgeSet.ncard+S.ncard := by
  classical
  have hsum := sum_neighbor_ncard (pairedCopies G S)
  rw [Fintype.sum_prod_type] at hsum
  simp_rw [pairedCopies_neighbor_ncard,Finset.sum_add_distrib,sum_neighbor_ncard] at hsum
  have hc : (∑ v : V, if v ∈ S then 1 else 0)=S.ncard := by
    simp only [←Finset.card_filter,Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp
  simp only [hc,Fintype.sum_bool] at hsum
  omega

lemma within_edge_ncard {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (within G S).edgeSet.ncard=(G.induce S).edgeSet.ncard := by
  let f : G.induce S →g within G S :=
    { toFun := Subtype.val, map_rel' := fun {x y} h ↦ ⟨h,x.property,y.property⟩ }
  have hc : (within G S).edgeSet=Sym2.map f '' (G.induce S).edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      induction e using Sym2.ind with
      | h x y => exact ⟨s(⟨x,he.2.1⟩,⟨y,he.2.2⟩),he.1,rfl⟩
    · rintro e ⟨a,ha,rfl⟩
      exact f.map_mem_edgeSet ha
  rw [hc]
  exact Set.ncard_image_of_injective _ (Sym2.map.injective (show Function.Injective f from Subtype.val_injective))

lemma bridge_cut_edge_ncard {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) :
    G.edgeSet.ncard=(G.induce S).edgeSet.ncard+(G.induce Sᶜ).edgeSet.ncard+1 := by
  classical
  have he : G.edgeSet=insert s(u,v) ((within G S).edgeSet ∪ (within G Sᶜ).edgeSet) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      constructor
      · intro hxy
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · exact Or.inr (Or.inl ⟨hxy,hx,hy⟩)
        · obtain ⟨rfl,rfl⟩ := hcross x hx y hy hxy
          exact Or.inl rfl
        · obtain ⟨rfl,rfl⟩ := hcross y hy x hx hxy.symm
          exact Or.inl Sym2.eq_swap
        · exact Or.inr (Or.inr ⟨hxy,hx,hy⟩)
      · rintro (he|hh|hh)
        · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact h
          · exact h.symm
        · exact hh.1
        · exact hh.1
  have hd : Disjoint (within G S).edgeSet (within G Sᶜ).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | h x y => exact hf.2.1 he.2.1
  have hn : s(u,v) ∉ (within G S).edgeSet ∪ (within G Sᶜ).edgeSet := by
    rintro (hh|hh)
    · exact hv hh.2.2
    · exact hh.2.1 hu
  rw [he,Set.ncard_insert_of_notMem hn,Set.ncard_union_eq hd,
    within_edge_ncard,within_edge_ncard]

/-- The half-order doubling argument also works at the boundary when the
joined double has fewer edges than the globally critical witness. -/
lemma marked_of_half_order_fewer_edges {n : ℕ} {G : SimpleGraph (Fin n)}
    (hmin : MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {V : Type*} [Fintype V] (H : SimpleGraph V) (hH : H.Connected) (r : V)
    (hsize : 2*Fintype.card V=n) (hedges : 2*H.edgeSet.ncard+1 < G.edgeSet.ncard) :
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ∧ MarkedAt D r := by
  obtain ⟨D,hD,hDc⟩ := hmin.on_finite (pairedCopies H {r})
    (by simpa only [Fintype.card_prod,Fintype.card_bool] using hsize)
    (pairedCopies_connected H hH {r} ⟨r,rfl⟩)
    (by simpa only [pairedCopies_edge_ncard,Set.ncard_singleton] using hedges)
  apply marked_of_double_bridge r hD
  simp only [Fintype.card_fin,ceil_half] at hDc
  omega

lemma failure_cut_side_edge_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hmin : MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : 2 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) :
    (G.induce Sᶜ).edgeSet.ncard ≤ (G.induce S).edgeSet.ncard := by
  classical
  by_contra hlt
  have hcard : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hbalance := failure_cut_balanced hsmall hG hfail S h hu hv hcross hS hcS
  have hconn := CutVertexReduction.single_boundary_connected hG S u hu
    (fun x hx y hy hxy ↦ (hcross x hx y hy hxy).1)
  have hE := bridge_cut_edge_ncard S h hu hv hcross
  obtain ⟨D,hD,hDc,a,p,hp,hm⟩ := marked_of_half_order_fewer_edges hmin (G.induce S) hconn ⟨u,hu⟩
    (by rw [hcard]; exact hbalance.2.1) (by omega)
  exact hfail (MarkedBudgets.gallai_of_marked_bridge_side hsmall hG S h hu hv hcross hS hD p hp hm
    (by simpa only [hcard] using hDc))

/-- The two nontrivial sides of a bridge have equal internal edge counts,
as well as the already established equal even vertex counts. -/
lemma failure_cut_edges_equal {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hmin : MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : 2 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) :
    (G.induce S).edgeSet.ncard=(G.induce Sᶜ).edgeSet.ncard := by
  have ha := failure_cut_side_edge_bound hsmall hG hfail hmin S h hu hv hcross hS hcS
  have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
    intro x hx y hy hxy
    exact (hcross y (by simpa only [Set.mem_compl_iff,not_not] using hy) x hx hxy.symm).symm
  have hb := failure_cut_side_edge_bound hsmall hG hfail hmin Sᶜ h.symm hv (not_not.mpr hu)
    hcross' hcS (by simpa only [compl_compl] using hS)
  have hb' : (G.induce S).edgeSet.ncard ≤ (G.induce Sᶜ).edgeSet.ncard := by
    simpa only [←within_edge_ncard,compl_compl] using hb
  exact Nat.le_antisymm hb' ha

lemma nonleaf_bridge_odd_edge_count {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hmin : MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v))
    (hu : Nat.card (G.neighborSet u) ≠ 1) (hv : Nat.card (G.neighborSet v) ≠ 1) :
    Odd G.edgeSet.ncard := by
  obtain ⟨S,huS,hvS,hcross,hS|hS|⟨k,hk,hS,hT,_⟩⟩ :=
    failure_bridge_balanced hsmall hG hfail hb
  · exact (hu (cut_singleton_degree S (isBridge_iff.mp hb).1 huS hcross hS)).elim
  · apply False.elim ∘ hv
    apply cut_singleton_degree Sᶜ (isBridge_iff.mp hb).1.symm hvS _ hS
    intro x hx y hy hxy
    exact (hcross y (by simpa only [Set.mem_compl_iff,not_not] using hy) x hx hxy.symm).symm
  · have he := failure_cut_edges_equal hsmall hG hfail hmin S (isBridge_iff.mp hb).1 huS hvS hcross
      (by omega) (by omega)
    have hc := bridge_cut_edge_ncard S (isBridge_iff.mp hb).1 huS hvS hcross
    exact ⟨(G.induce S).edgeSet.ncard,by omega⟩

lemma bridge_leaf_of_even_edge_count {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hmin : MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (he : Even G.edgeSet.ncard) {u v : Fin n} (hb : G.IsBridge s(u,v)) :
    Nat.card (G.neighborSet u)=1 ∨ Nat.card (G.neighborSet v)=1 := by
  by_contra! hn
  exact (Nat.not_even_iff_odd.mpr (nonleaf_bridge_odd_edge_count hsmall hG hfail hmin hb hn.1 hn.2)) he

lemma one_leaf_of_even_edge_count {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hmin : MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (he : Even G.edgeSet.ncard) :
    (Finset.univ.filter fun u ↦ Nat.card (G.neighborSet u)=1).card ≤ 1 := by
  classical
  by_contra hn
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (by omega :
    1 < (Finset.univ.filter fun u ↦ Nat.card (G.neighborSet u)=1).card)
  obtain ⟨a,ha,hu'⟩ := LeafPairReduction.leaf_data (Finset.mem_filter.mp hu).2
  obtain ⟨b,hb,hv'⟩ := LeafPairReduction.leaf_data (Finset.mem_filter.mp hv).2
  have hab := LeafPairReduction.leaf_neighbors_bridge_of_failure hsmall hG hfail huv ha hb hu' hv'
  have hna := LeafPairReduction.leaf_neighbor_not_leaf_of_failure hG hfail ha hu'
  have hnb := LeafPairReduction.leaf_neighbor_not_leaf_of_failure hG hfail hb hv'
  exact (bridge_leaf_of_even_edge_count hsmall hG hfail hmin he hab.2).elim hna hnb

end Erdos583GlobalCriticalDevelopment
