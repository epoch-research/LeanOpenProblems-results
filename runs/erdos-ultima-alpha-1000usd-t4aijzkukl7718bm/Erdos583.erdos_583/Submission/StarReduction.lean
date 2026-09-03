import Submission.PortSplicing
import Submission.StarExternalPaths

/-! A rooted core cover whose boundary edges occupy distinct paths gives a vertex-reduction. -/
namespace Erdos583StarReductionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.BridgeGlue
open Erdos583StarPathPiecesDevelopment Erdos583BoundaryPortsDevelopment
open Erdos583StarContractionDevelopment Erdos583StarExternalPathsDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V} {S : Set V}
  (start : I → V) (core : ∀ i, Arm G (start i))
  (hc : ∀ i, ∀ x ∈ (core i).walk.support, x ∈ S)
  (hcc : Pairwise (fun i j ↦ Disjoint (core i).walk.toSubgraph.edgeSet (core j).walk.toSubgraph.edgeSet))
  (hcore : (⋃ i, (core i).walk.toSubgraph.edgeSet)=(within G S).edgeSet)
  (hcap : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤
      (G.neighborSet v ∩ S).ncard+Fintype.card {i : I // start i=v})

include hc hcc hcore hcap in
lemma lift_partition {r : V} (hr : r ∈ S) {k : ℕ}
    (T : TrailFamily (contract G S r hr) k) (hp : ∀ i, (T.walk i).IsPath)
    (htouch : ∃ i, r ∈ (T.walk i).support) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card+1 ≤ k+Fintype.card I := by
  obtain ⟨slot,hslot⟩ := assign G S start hcap
  obtain ⟨D,hD,hn⟩ := Erdos583PortSplicingDevelopment.decomposition start core slot hslot
    (exterior hr T hp) (avoiding hr T) hc (exterior_outside hr T hp) (avoiding_subset hr T)
    hcc (exterior_disjoint hr T hp) (avoiding_disjoint hr T) (avoiding_exterior_disjoint hr T hp)
    (avoiding_isPath hr T hp) hcore (exterior_cover hr T hp)
  have ha := avoid_index_card_lt T r htouch
  exact ⟨D,hD,by omega⟩

omit [Fintype V] in
lemma boundary_nonempty {r : V} (hr : r ∈ S) (hG : G.Connected) (hS : S ≠ Set.univ) :
    Nonempty (Boundary G S) := by
  by_contra hn
  apply hS
  apply TrailBudget.connected_closed_set hG S ⟨r,hr⟩
  intro x y hxy hx
  by_contra hy
  exact hn ⟨⟨(⟨x,hx⟩,⟨y,hy⟩),hxy⟩⟩

omit [Fintype V] in
lemma partition_touches_center {r : V} (hr : r ∈ S) (hG : G.Connected) (hS : S ≠ Set.univ)
    {k : ℕ} (T : TrailFamily (contract G S r hr) k) : ∃ i, r ∈ (T.walk i).support := by
  obtain ⟨b⟩ := boundary_nonempty hr hG hS
  have hadj : (contract G S r hr).Adj r (outer G S b) :=
    (adj_center G S r hr).mpr ⟨outer_not_mem G S b,inner G S b,inner_mem G S b,adj G S b⟩
  obtain ⟨i,hi⟩ := (T.cover s(r,outer G S b)).mp hadj
  exact ⟨i,Walk.mem_support_of_adj_toSubgraph hi⟩

include hc hcc hcore hcap in
lemma reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n) (hn : Fintype.card V=n)
    (hG : G.Connected) (hS : S ≠ Set.univ) (hsize : 2 ≤ S.ncard)
    (hbudget : 2*Fintype.card I ≤ S.ncard+1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite S)).mp (by omega : 0 < S.ncard)
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
  obtain ⟨F,hF,hFc⟩ := lift_partition start core hc hcc hcore hcap hr T hT
    (partition_touches_center hr hG hS T)
  refine ⟨F,hF,?_⟩
  rw [ceil_half] at hDc ⊢
  omega

omit [Fintype V] in
include hcc hcore in
lemma full_partition (hS : S=Set.univ) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ Fintype.card I := by
  let f (i : I) := (core i).walk.toSubgraph
  let D := Finset.univ.image f
  have he : (within G S).edgeSet=G.edgeSet := by
    rw [hS]
    ext e
    induction e using Sym2.ind with
    | h x y => exact ⟨And.left,fun h ↦ ⟨h,Set.mem_univ _,Set.mem_univ _⟩⟩
  refine ⟨D,⟨?_,?_,?_⟩,Finset.card_image_le.trans (by simp)⟩
  · intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact ⟨_,_,_,(core i).isPath,rfl⟩
  · intro K hK L hL hKL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact hcc (fun hij ↦ hKL (congrArg f hij))
  · have hh : (⋃ i, (f i).edgeSet)=G.edgeSet := hcore.trans he
    simpa only [D,Finset.mem_image,Finset.mem_univ,true_and,Set.iUnion_exists,
      Set.iUnion_iUnion_eq',Set.iUnion_iUnion_eq_left] using hh

include hc hcc hcore hcap in
lemma reduction_or_full {n : ℕ} (hsmall : VertexCritical.SmallerOrders n) (hn : Fintype.card V=n)
    (hG : G.Connected) (hsize : 2 ≤ S.ncard) (hbudget : 2*Fintype.card I ≤ S.ncard+1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  by_cases hS : S=Set.univ
  · obtain ⟨D,hD,hDc⟩ := full_partition start core hcc hcore hS
    rw [hS,Set.ncard_univ,Nat.card_eq_fintype_card] at hbudget
    exact ⟨D,hD,by rw [ceil_half]; omega⟩
  · exact reduction start core hc hcc hcore hcap hsmall hn hG hS hsize hbudget

end Erdos583StarReductionDevelopment
