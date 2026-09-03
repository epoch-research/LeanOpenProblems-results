import Submission.Work

/-! Edge-minimal failures and the complete range of edge-restoration roots.
These are structural necessary conditions, not a proof of Gallai's bound. -/
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted
namespace Erdos583EdgeCriticalDevelopment

/-- All connected spanning subgraphs with strictly fewer edges meet the
specified budget. No vertex-minimality is asserted. -/
def EdgeMinimal {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : SimpleGraph V, H ≤ G → H.Connected → H.edgeSet.ncard < G.edgeSet.ncard →
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k

lemma exists_edge_minimal_failure {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (k : ℕ)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k) ∧
      EdgeMinimal H k := by
  classical
  let P (n : ℕ) := ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
    (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ k) ∧ H.edgeSet.ncard=n
  have hex : ∃ n, P n := ⟨G.edgeSet.ncard,G,le_rfl,hG,hfail,rfl⟩
  obtain ⟨H,hHG,hH,hfailH,hmin⟩ := Nat.find_spec hex
  refine ⟨H,hHG,hH,hfailH,?_⟩
  intro J hJH hJ hlt
  by_contra hno
  have hbound := Nat.find_min' hex (show P J.edgeSet.ncard from
    ⟨J,hJH.trans hHG,hJ,hno,rfl⟩)
  omega

lemma EdgeMinimal.delete_nonbridge {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hmin : EdgeMinimal G k) (hG : G.Connected)
    {u v : V} (h : G.Adj v u) (hnb : ¬G.IsBridge s(v,u)) :
    ∃ D : Finset (G.deleteEdges {s(v,u)}).Subgraph,
      GoodDecomposition (G.deleteEdges {s(v,u)}) D ∧ D.card ≤ k := by
  apply hmin _ (G.deleteEdges_le _) (hG.connected_delete_edge_of_not_isBridge hnb)
  rw [edgeSet_deleteEdges]
  exact Set.ncard_diff_singleton_lt_of_mem (show s(v,u) ∈ G.edgeSet from h)

/-- The root is available at every eligible other endpoint, not only at the
single endpoint selected by the original counterexample reduction. -/
lemma EdgeMinimal.root_at_other_endpoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hmin : EdgeMinimal G k) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (hnb : ¬G.IsBridge s(v,u)) :
    ∃ T : TrailFamily G k, T.score+1=G.edgeSet.ncard+k ∧ HasRoot T v ∧
      ∀ U : TrailFamily G k, U.score ≤ T.score := by
  obtain ⟨D,hD,hcard⟩ := hmin.delete_nonbridge hG h hnb
  exact EdgeDefect.one_defect_of_even_edge_deletion h hu k D hD hcard hfail

/-- Under the even-forest condition, restoring an edge whose two endpoints
become even does not increase any available path budget. Connectivity and
minimality are not needed for this restoration lemma. -/
lemma restore_even_even_edge_of_even_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v)))
    (hforest : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic)
    (D : Finset (G.deleteEdges {s(v,u)}).Subgraph)
    (hD : GoodDecomposition (G.deleteEdges {s(v,u)}) D) (hcard : D.card ≤ k) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ k := by
  by_contra hfail
  obtain ⟨T,hs,hr,hm⟩ := EdgeDefect.one_defect_of_even_edge_deletion h hu k D hD hcard hfail
  obtain ⟨P,hP⟩ := QuotaParity.normalize_even_root_of_even_forest T v hs hr hv hforest
  exact RootEnergy.maximum_defect_no_paths T hs hm P hP

/-- An even-even edge cannot be a nonbridge in an edge-minimal failure whose
even-degree induced graph is acyclic. This does not settle the odd-root case. -/
lemma EdgeMinimal.even_even_edge_isBridge_of_even_forest {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hmin : EdgeMinimal G k) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (hforest : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic)
    {u v : V} (h : G.Adj v u) (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) : G.IsBridge s(v,u) := by
  by_contra hnb
  obtain ⟨T,hs,hr,hm⟩ := hmin.root_at_other_endpoint hG hfail h hu hnb
  obtain ⟨P,hP⟩ := QuotaParity.normalize_even_root_of_even_forest T v hs hr hv hforest
  exact RootEnergy.maximum_defect_no_paths T hs hm P hP

/-- Keep the edge-minimality certificate alongside the rooted single defect
at the exact Gallai budget. -/
lemma failure_has_edge_minimal_rooted_one_defect {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) ∧
      EdgeMinimal H ⌈(Fintype.card V : ℚ)/2⌉₊ ∧
      ∃ r : V, ∃ T : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊,
        T.score+1=H.edgeSet.ncard+⌈(Fintype.card V : ℚ)/2⌉₊ ∧ HasRoot T r ∧
        ∀ U : TrailFamily H ⌈(Fintype.card V : ℚ)/2⌉₊, U.score ≤ T.score := by
  obtain ⟨H,hHG,hH,hfailH,hmin⟩ := exists_edge_minimal_failure G hG _ hfail
  obtain ⟨u,v,h,hu,hnb⟩ := EdgeDefect.failure_has_even_nonbridge H hfailH
  obtain ⟨T,hs,hr,hm⟩ := hmin.root_at_other_endpoint hH hfailH h hu hnb
  exact ⟨H,hHG,hH,hfailH,hmin,v,T,hs,hr,hm⟩

end Erdos583EdgeCriticalDevelopment
