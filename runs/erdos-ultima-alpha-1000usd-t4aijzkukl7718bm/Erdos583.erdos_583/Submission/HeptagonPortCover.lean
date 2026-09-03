import Submission.HeptagonPortLabels
import Submission.StarReduction

/-! Transport the four-port covers to an arbitrary induced seven-vertex core. -/
namespace Erdos583HeptagonPortCoverDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583StarPathPiecesDevelopment Erdos583HeptagonPortLabelsDevelopment
open scoped Classical
set_option maxHeartbeats 2200000

lemma induced_neighbor_card {V : Type*} (G : SimpleGraph V) (S : Set V) (v : S) :
    Nat.card ((G.induce S).neighborSet v)=(G.neighborSet v.val ∩ S).ncard := by
  let e : (G.induce S).neighborSet v ≃ (G.neighborSet v.val ∩ S : Set V) :=
    { toFun := fun x ↦ ⟨x.val.val,x.property,x.val.property⟩
      invFun := fun y ↦ ⟨⟨y.val,y.property.2⟩,y.property.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; rfl }
  rw [Nat.card_congr e,Nat.card_coe_set_eq]

section Iso
variable {V : Type*} {G : SimpleGraph V} {S : Set V} {c : Bool}
  (e : Erdos583HeptagonPortRoutesDevelopment.graph c ≃g G.induce S)

def inclusion : Erdos583HeptagonPortRoutesDevelopment.graph c →g G :=
  (Embedding.induce S).toHom.comp e.toHom

lemma inclusion_injective : Function.Injective (inclusion e) :=
  Subtype.val_injective.comp e.injective

def start (i : Fin 4) : V := inclusion e (Erdos583HeptagonPortRoutesDevelopment.start c i)

def paths (i : Fin 4) : Arm G (start e i) :=
  { finish := inclusion e (Erdos583HeptagonPortRoutesDevelopment.finish c i)
    walk := (Erdos583HeptagonPortRoutesDevelopment.walk c i).map (inclusion e)
    isPath := Walk.map_isPath_of_injective (inclusion_injective e)
      (Erdos583HeptagonPortRoutesDevelopment.walk_isPath c i) }

lemma paths_inside (i : Fin 4) : ∀ x ∈ (paths e i).walk.support, x ∈ S := by
  intro x hx
  change x ∈ ((Erdos583HeptagonPortRoutesDevelopment.walk c i).map (inclusion e)).support at hx
  rw [Walk.support_map,List.mem_map] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact (e y).property

lemma paths_disjoint : Pairwise (fun i j ↦ Disjoint (paths e i).walk.toSubgraph.edgeSet
    (paths e j).walk.toSubgraph.edgeSet) := by
  intro i j hij
  change Disjoint ((Erdos583HeptagonPortRoutesDevelopment.walk c i).map (inclusion e)).toSubgraph.edgeSet
    ((Erdos583HeptagonPortRoutesDevelopment.walk c j).map (inclusion e)).toSubgraph.edgeSet
  rw [Walk.toSubgraph_map,Walk.toSubgraph_map,Subgraph.edgeSet_map,Subgraph.edgeSet_map,
    Set.disjoint_image_iff (Sym2.map.injective (inclusion_injective e))]
  exact Erdos583HeptagonPortRoutesDevelopment.walk_disjoint c hij

lemma paths_cover : (⋃ i, (paths e i).walk.toSubgraph.edgeSet)=(within G S).edgeSet := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun i ↦ Erdos583PortSplicingDevelopment.path_edges_inside (paths e i) (paths_inside e i))
  · intro d hd
    induction d using Sym2.ind with
    | h x y =>
      let a := e.symm ⟨x,hd.2.1⟩
      let b := e.symm ⟨y,hd.2.2⟩
      have ha : inclusion e a=x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hd.2.1⟩)
      have hb : inclusion e b=y := congrArg Subtype.val (e.apply_symm_apply ⟨y,hd.2.2⟩)
      have hab : (Erdos583HeptagonPortRoutesDevelopment.graph c).Adj a b := e.symm.map_adj_iff.mpr hd.1
      obtain ⟨i,hi⟩ := (Erdos583HeptagonPortRoutesDevelopment.walk_cover c s(a,b)).mp hab
      refine Set.mem_iUnion.mpr ⟨i,?_⟩
      change s(x,y) ∈ ((Erdos583HeptagonPortRoutesDevelopment.walk c i).map (inclusion e)).toSubgraph.edgeSet
      rw [Walk.toSubgraph_map,Subgraph.edgeSet_map]
      exact ⟨s(a,b),hi,by change s(inclusion e a,inclusion e b)=s(x,y); rw [ha,hb]⟩

variable [Fintype V]

omit [Fintype V] in
lemma start_fiber (v : S) :
    Fintype.card {i : Fin 4 // start e i=v.val}=
      Fintype.card {i : Fin 4 // Erdos583HeptagonPortRoutesDevelopment.start c i=e.symm v} := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change (e (Erdos583HeptagonPortRoutesDevelopment.start c i)).val=v.val ↔ _
  rw [←Subtype.ext_iff]
  exact e.toEquiv.eq_symm_apply.symm

omit [Fintype V] in
lemma paths_capacity (v : S) :
    (G.neighborSet v.val ∩ S).ncard+Fintype.card {i : Fin 4 // start e i=v.val}=6 := by
  have hd := Nat.card_congr (e.mapNeighborSet (e.symm v))
  rw [e.apply_symm_apply,induced_neighbor_card] at hd
  have hp := Erdos583HeptagonPortRoutesDevelopment.port_degree c (e.symm v)
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hd
  rw [start_fiber,←hd]
  omega

end Iso

lemma exists_cover {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hS : S.ncard=7) (hc : (G.induce S)ᶜ.edgeSet.ncard=2)
    (hdegree : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤ 6) :
    ∃ start : Fin 4 → V, ∃ core : ∀ i, Arm G (start i),
      (∀ i, ∀ x ∈ (core i).walk.support, x ∈ S) ∧
      Pairwise (fun i j ↦ Disjoint (core i).walk.toSubgraph.edgeSet (core j).walk.toSubgraph.edgeSet) ∧
      (⋃ i, (core i).walk.toSubgraph.edgeSet)=(within G S).edgeSet ∧
      ∀ v ∈ S, Nat.card (G.neighborSet v) ≤
        (G.neighborSet v ∩ S).ncard+Fintype.card {i : Fin 4 // start i=v} := by
  have hcard : Fintype.card S=7 := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,hS]
  obtain ⟨c,⟨e⟩⟩ := exists_core_iso_finite (G.induce S) hcard hc
  refine ⟨start e,paths e,paths_inside e,paths_disjoint e,paths_cover e,?_⟩
  intro v hv
  rw [paths_capacity e ⟨v,hv⟩]
  exact hdegree v hv

lemma core_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (S : Set (Fin n))
    (hS : S.ncard=7) (hc : (G.induce S)ᶜ.edgeSet.ncard=2)
    (hdegree : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤ 6) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨start,core,hinside,hdis,hcover,hcap⟩ := exists_cover G S hS hc hdegree
  apply Erdos583StarReductionDevelopment.reduction_or_full start core hinside hdis hcover hcap
    hsmall (Fintype.card_fin n) hG (by omega)
  simpa only [Fintype.card_fin,hS] using (by decide : 2*4 ≤ 7+1)

end Erdos583HeptagonPortCoverDevelopment
