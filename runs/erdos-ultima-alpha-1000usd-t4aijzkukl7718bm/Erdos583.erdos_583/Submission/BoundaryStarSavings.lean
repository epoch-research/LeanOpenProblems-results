import Submission.StarCopyIntegrated

/-! Degree-sensitive lifting from a contracted core. These are conditional
vertex reductions, not a proof of the unrestricted path bound. -/
namespace Erdos583BoundaryStarSavingsDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.BridgeGlue
open Erdos583Work.StarPathPieces Erdos583Work.BoundaryPorts
open Erdos583Work.StarContraction Erdos583Work.StarExternalPaths
open scoped Classical
set_option maxHeartbeats 1600000
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V} {S : Set V}
  (start : I → V) (core : ∀ i, Arm G (start i))
  (hc : ∀ i, ∀ x ∈ (core i).walk.support, x ∈ S)
  (hcc : Pairwise (fun i j ↦ Disjoint (core i).walk.toSubgraph.edgeSet (core j).walk.toSubgraph.edgeSet))
  (hcore : (⋃ i, (core i).walk.toSubgraph.edgeSet)=(within G S).edgeSet)
  (hcap : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤
      (G.neighborSet v ∩ S).ncard+Fintype.card {i : I // start i=v})

include hc hcc hcore hcap in
lemma lift_partition_degree {r : V} (hr : r ∈ S) {k : ℕ}
    (T : TrailFamily (contract G S r hr) k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card+Nat.card ((contract G S r hr).neighborSet r) ≤ 2*k+2*Fintype.card I := by
  obtain ⟨slot,hslot⟩ := assign G S start hcap
  obtain ⟨D,hD,hn⟩ := PortSplicing.decomposition start core slot hslot
    (exterior hr T hp) (avoiding hr T) hc (exterior_outside hr T hp) (avoiding_subset hr T)
    hcc (exterior_disjoint hr T hp) (avoiding_disjoint hr T) (avoiding_exterior_disjoint hr T hp)
    (avoiding_isPath hr T hp) hcore (exterior_cover hr T hp)
  have hdeg := MatchingCutGlue.degree_add_twice_avoid_le T hp r
  simp only [Nat.card_eq_fintype_card] at hdeg ⊢
  exact ⟨D,hD,by omega⟩

include hc hcc hcore hcap in
lemma reduction_degree {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hsize : 2 ≤ S.ncard) {r : V} (hr : r ∈ S)
    (hbudget : 2*Fintype.card I+1 ≤ S.ncard+Nat.card ((contract G S r hr).neighborSet r)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  let K := contract G S r hr
  let U := Sᶜ ∪ {r}
  have hcU : U.ncard+S.ncard=Fintype.card V+1 := card_vertices S r hr
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce K U (by omega) (connected_induce G S r hr hG)
  obtain ⟨E,hE,hEc⟩ := lift_induce_within U D hD
  have hKU : within K U=K := within_eq G S r hr
  have hex : ∃ E : Finset K.Subgraph, GoodDecomposition K E ∧ E.card ≤ D.card := by
    exact Eq.mp (congrArg (fun J : SimpleGraph V ↦
      ∃ F : Finset J.Subgraph, GoodDecomposition J F ∧ F.card ≤ D.card) hKU) ⟨E,hE,hEc⟩
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨T,hT,_⟩ := EdgeDefect.decomposition_path_family E hE
  obtain ⟨F,hF,hFc⟩ := lift_partition_degree start core hc hcc hcore hcap hr T hT
  refine ⟨F,hF,?_⟩
  rw [ceil_half] at hDc ⊢
  omega

include hc hcc hcore hcap in
lemma reduction_degree_odd {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (ho : Odd n) (hG : G.Connected)
    (hsize : 2 ≤ S.ncard) {r : V} (hr : r ∈ S)
    (hbudget : 2*Fintype.card I ≤ S.ncard+Nat.card ((contract G S r hr).neighborSet r)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  let K := contract G S r hr
  let U := Sᶜ ∪ {r}
  have hcU : U.ncard+S.ncard=Fintype.card V+1 := card_vertices S r hr
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce K U (by omega) (connected_induce G S r hr hG)
  obtain ⟨E,hE,hEc⟩ := lift_induce_within U D hD
  have hKU : within K U=K := within_eq G S r hr
  have hex : ∃ E : Finset K.Subgraph, GoodDecomposition K E ∧ E.card ≤ D.card := by
    exact Eq.mp (congrArg (fun J : SimpleGraph V ↦
      ∃ F : Finset J.Subgraph, GoodDecomposition J F ∧ F.card ≤ D.card) hKU) ⟨E,hE,hEc⟩
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨T,hT,_⟩ := EdgeDefect.decomposition_path_family E hE
  obtain ⟨F,hF,hFc⟩ := lift_partition_degree start core hc hcc hcore hcap hr T hT
  refine ⟨F,hF,?_⟩
  rw [ceil_half] at hDc ⊢
  obtain ⟨m,hm⟩ := ho
  omega

end Erdos583BoundaryStarSavingsDevelopment
