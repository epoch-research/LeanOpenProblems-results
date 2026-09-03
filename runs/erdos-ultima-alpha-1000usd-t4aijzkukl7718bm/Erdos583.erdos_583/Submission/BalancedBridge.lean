import Submission.Work
import Submission.MarkedDouble

/-! Uniqueness of a balanced bridge cut and consequences for smallest-order
path-decomposition failures. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
open Erdos583MarkedDoubleDevelopment
namespace Erdos583BalancedBridgeDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- A connected induced set avoiding both endpoints of a one-edge cut lies
entirely on one side of that cut. -/
lemma connected_set_one_side {V : Type*} {G : SimpleGraph V}
    (S U : Set V) (hU : (G.induce U).Connected) {u v : V}
    (hu : u ∉ U) (hv : v ∉ U)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) :
    U ⊆ S ∨ U ⊆ Sᶜ := by
  classical
  let a : U := Classical.choice hU.nonempty
  by_cases ha : a.val ∈ S
  · left
    intro x hx
    exact reachable_mem_of_closed (G := G.induce U) (T := {z | z.val ∈ S})
      (fun y hy z hyz ↦ by
        by_contra hz
        have he := (hcross y.val hy z.val hz hyz).1
        exact hu (he ▸ y.property)) (hU.preconnected a ⟨x,hx⟩) ha
  · right
    intro x hx
    exact reachable_mem_of_closed (G := G.induce U) (T := {z | z.val ∉ S})
      (fun y hy z hyz ↦ by
        intro hz
        have he := (hcross z.val hz y.val hy hyz.symm).2
        exact hv (he ▸ y.property)) (hU.preconnected a ⟨x,hx⟩) ha

lemma half_set_meets_cut_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S U : Set V) (hU : (G.induce U).Connected) {u v : V}
    (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : S.ncard=Sᶜ.ncard) (hUS : U.ncard=S.ncard) : u ∈ U ∨ v ∈ U := by
  by_contra! hn
  rcases connected_set_one_side S U hU hn.1 hn.2 hcross with hs|hs
  · have he : U=S := Set.eq_of_subset_of_ncard_le hs (by omega)
    exact hn.1 (he.symm ▸ hu)
  · have he : U=Sᶜ := Set.eq_of_subset_of_ncard_le hs (by omega)
    exact hn.2 (he.symm ▸ hv)

/-- In any finite connected graph, two one-edge cuts with equally sized sides
must be the same edge. -/
lemma balanced_cut_unique {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) (S T : Set V) {u v a b : V}
    (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hSx : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (ha : a ∈ T) (hb : b ∉ T)
    (hTx : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y → x=a ∧ y=b)
    (hS : S.ncard=Sᶜ.ncard) (hT : T.ncard=Tᶜ.ncard) : s(u,v)=s(a,b) := by
  by_contra hn
  have hsz : T.ncard=S.ncard := by
    have hs := S.ncard_add_ncard_compl
    have ht := T.ncard_add_ncard_compl
    omega
  by_cases huT : u ∈ T
  · have hvT : v ∈ T := by
      by_contra hvT
      obtain ⟨hua,hvb⟩ := hTx u huT v hvT h
      exact hn (by rw [hua,hvb])
    have hconn : (G.induce Tᶜ).Connected := CutVertexReduction.single_boundary_connected hG Tᶜ b hb (by
      intro x hx y hy hxy
      have hyT : y ∈ T := by simpa only [Set.mem_compl_iff,not_not] using hy
      exact (hTx y hyT x hx hxy.symm).2)
    rcases half_set_meets_cut_endpoints S Tᶜ hconn hu hv hSx hS (by omega) with hh|hh
    · exact hh huT
    · exact hh hvT
  · have hvT : v ∉ T := by
      intro hvT
      obtain ⟨hva,hub⟩ := hTx v hvT u huT h.symm
      exact hn (by rw [hva,hub]; exact Sym2.eq_swap)
    have hconn := CutVertexReduction.single_boundary_connected hG T a ha
      (fun x hx y hy hxy ↦ (hTx x hx y hy hxy).1)
    rcases half_set_meets_cut_endpoints S T hconn hu hv hSx hS hsz with hh|hh
    · exact huT hh
    · exact hvT hh

lemma balanced_cut_of_nonleaf_bridge {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v))
    (hu : Nat.card (G.neighborSet u) ≠ 1) (hv : Nat.card (G.neighborSet v) ≠ 1) :
    ∃ S : Set (Fin n), u ∈ S ∧ v ∉ S ∧
      (∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) ∧ S.ncard=Sᶜ.ncard := by
  obtain ⟨S,huS,hvS,hcross,hS|hS|⟨k,_,hs,ht,_⟩⟩ := failure_bridge_balanced hsmall hG hfail hb
  · exact (hu (cut_singleton_degree S (isBridge_iff.mp hb).1 huS hcross hS)).elim
  · apply False.elim ∘ hv
    apply cut_singleton_degree Sᶜ (isBridge_iff.mp hb).1.symm hvS _ hS
    intro x hx y hy hxy
    have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hyS x hx hxy.symm).symm
  · exact ⟨S,huS,hvS,hcross,hs.trans ht.symm⟩

/-- A smallest-order failure has at most one bridge with no leaf endpoint. -/
lemma nonleaf_bridge_unique_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v a b : Fin n} (huv : G.IsBridge s(u,v)) (hab : G.IsBridge s(a,b))
    (hu : Nat.card (G.neighborSet u) ≠ 1) (hv : Nat.card (G.neighborSet v) ≠ 1)
    (ha : Nat.card (G.neighborSet a) ≠ 1) (hb : Nat.card (G.neighborSet b) ≠ 1) :
    s(u,v)=s(a,b) := by
  obtain ⟨S,huS,hvS,hSx,hS⟩ := balanced_cut_of_nonleaf_bridge hsmall hG hfail huv hu hv
  obtain ⟨T,haT,hbT,hTx,hT⟩ := balanced_cut_of_nonleaf_bridge hsmall hG hfail hab ha hb
  exact balanced_cut_unique hG S T (isBridge_iff.mp huv).1 huS hvS hSx haT hbT hTx hS hT

lemma two_leaves_four_dvd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v) (hu : Nat.card (G.neighborSet u)=1)
    (hv : Nat.card (G.neighborSet v)=1) : 4 ∣ n := by
  obtain ⟨a,ha,hu'⟩ := LeafPairReduction.leaf_data hu
  obtain ⟨b,hb,hv'⟩ := LeafPairReduction.leaf_data hv
  have hbr := (LeafPairReduction.leaf_neighbors_bridge_of_failure hsmall hG hfail huv ha hb hu' hv').2
  have hla := LeafPairReduction.leaf_neighbor_not_leaf_of_failure hG hfail ha hu'
  have hlb := LeafPairReduction.leaf_neighbor_not_leaf_of_failure hG hfail hb hv'
  exact (bridge_leaf_or_four_dvd hsmall hG hfail hbr).resolve_left hla |>.resolve_left hlb

lemma one_leaf_unless_four_dvd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hn : ¬4 ∣ n) :
    (Finset.univ.filter fun u ↦ Nat.card (G.neighborSet u)=1).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra huv
  exact hn (two_leaves_four_dvd hsmall hG hfail huv (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2)

end Erdos583BalancedBridgeDevelopment
