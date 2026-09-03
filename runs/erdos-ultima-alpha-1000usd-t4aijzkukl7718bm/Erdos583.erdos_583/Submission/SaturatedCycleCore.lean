import Submission.CompleteCoreSplicing

/-! Saturated even cycle cores. A cardinality equality forces the core to be
complete, and parity then supplies the distinct endpoint ports for splicing. -/
namespace Erdos583SaturatedCycleCoreDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CompletePrescribedPairsDevelopment
open Erdos583CompleteCoreSplicingDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma full_edge_count_eq_top {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hc : H.edgeSet.ncard=(Fintype.card V).choose 2) : H=⊤ := by
  classical
  have ht : (⊤ : SimpleGraph V).edgeSet.ncard=(Fintype.card V).choose 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact card_edgeFinset_top_eq_card_choose_two
  have he : H.edgeSet=(⊤ : SimpleGraph V).edgeSet :=
    Set.eq_of_subset_of_ncard_le (edgeSet_mono le_top) (by omega)
  ext u v
  change s(u,v) ∈ H.edgeSet ↔ s(u,v) ∈ (⊤ : SimpleGraph V).edgeSet
  rw [he]

lemma cycle_piece_saturation {V : Type*} [Fintype V] {H : SimpleGraph V}
    {k : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (a b : Fin k → V) (p : ∀ i, H.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsTrail)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=H.edgeSet)
    (hcard : 2*k=Fintype.card V)
    (hload : C.length+∑ i, (p i).length=(Fintype.card V).choose 2) :
    H=⊤ ∧ Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1) := by
  classical
  have hdis : Disjoint C.toSubgraph.edgeSet (⋃ i, (p i).toSubgraph.edgeSet) := by
    apply Set.disjoint_left.mpr
    intro e heC hep
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hep
    exact Set.disjoint_left.mp (hCp i) heC hi
  have hsize : H.edgeSet.ncard=(Fintype.card V).choose 2 := by
    rw [←hc,Set.ncard_union_eq hdis,trail_edgeSet_ncard C hC.isTrail,
      Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hd,finsum_eq_sum_of_fintype]
    simpa only [trail_edgeSet_ncard _ (hp _)] using hload
  have htop := full_edge_count_eq_top H hsize
  have hedge (i : Fin k) : ∀ e ∈ (p i).edges, e ∈ (H.deleteEdges C.toSubgraph.edgeSet).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    refine ⟨(p i).edges_subset_edgeSet he,?_⟩
    intro heC
    exact Set.disjoint_left.mp (hCp i) heC ((p i).mem_edges_toSubgraph.mpr he)
  let q (i : Fin k) := (p i).transfer (H.deleteEdges C.toSubgraph.edgeSet) (hedge i)
  have hqe (i : Fin k) : (q i).toSubgraph.edgeSet=(p i).toSubgraph.edgeSet := by
    ext e
    simp only [q,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  let T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) k :=
    { start := a
      finish := b
      walk := q
      isTrail := fun i ↦ by
        simpa only [q,Walk.isTrail_def,Walk.edges_transfer] using hp i
      disjoint := fun i j hij ↦ by
        change Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet
        rw [hqe,hqe]
        exact hd hij
      cover := fun e ↦ by
        simp only [hqe,edgeSet_deleteEdges,Set.mem_diff]
        constructor
        · rintro ⟨heH,heC⟩
          rw [←hc] at heH
          exact Set.mem_iUnion.mp (heH.resolve_left heC)
        · rintro ⟨i,hi⟩
          exact ⟨(p i).toSubgraph.edgeSet_subset hi,
            fun heC ↦ Set.disjoint_left.mp (hCp i) heC hi⟩ }
  refine ⟨htop,sharp_odd_endpoint_bijective T hcard ?_⟩
  intro v
  have ht : Nat.card (H.neighborSet v)=Nat.card ((⊤ : SimpleGraph V).neighborSet v) := by rw [htop]
  have ho : Odd (Nat.card (H.neighborSet v)) := by
    rw [ht]
    exact complete_even_degree_odd hcard v
  rw [Nat.card_coe_set_eq,Nat.odd_iff] at ho ⊢
  exact (delete_cycle_preserves_degree_parity hC v).trans ho

/-- The edge-count equality follows from the core-vertex incidence count
arising when one spanning carrier has been cut into two core pieces. -/
lemma cycle_piece_incidence_saturation {V : Type*} [Fintype V] {H : SimpleGraph V}
    {k : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (hspan : C.toSubgraph.verts=Set.univ)
    (a b : Fin k → V) (p : ∀ i, H.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=H.edgeSet)
    (hcard : 2*k=Fintype.card V)
    (hinc : (∑ i, (p i).toSubgraph.verts.ncard)=(k-1)*Fintype.card V) :
    H=⊤ ∧ Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1) := by
  classical
  have hlen : C.length=Fintype.card V := by
    have hv : C.toSubgraph.verts.ncard=C.length := by
      rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
    rw [hspan,Set.ncard_univ,Nat.card_eq_fintype_card] at hv
    exact hv.symm
  have hsum : (∑ i, (p i).length)+k=(k-1)*Fintype.card V := by
    have hvertices := fun i ↦ InducedBuffer.path_vertex_ncard (p i) (hp i)
    simpa only [hvertices,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one] using hinc
  have hchoose : (Fintype.card V).choose 2=k*(2*k-1) := by
    rw [←hcard,Nat.choose_two_right]
    simp [Nat.mul_assoc]
  have h3 := hC.three_le_length
  have hk : 1 ≤ k := by omega
  have hk' : k-1+1=k := Nat.sub_add_cancel hk
  have hload : C.length+(∑ i, (p i).length)=(Fintype.card V).choose 2 := by
    rw [hchoose]
    have hs : 2*k-1+1=2*k := Nat.sub_add_cancel (by omega)
    nlinarith
  exact cycle_piece_saturation C hC a b p (fun i ↦ (hp i).isTrail) hd hCp hc hcard hload

/-- A saturated cycle core can be rerouted at the same number of core-piece
slots, with no restriction on intersections between different exterior pairs.
The explicit incidence and exterior-pair conditions are essential hypotheses. -/
lemma saturated_cycle_core_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} {r : S}
    (C : (G.induce S).Walk r r) (hC : C.IsCycle)
    (hspan : C.toSubgraph.verts=Set.univ)
    (a b : Fin k → S) (p : ∀ i, (G.induce S).Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=(G.induce S).edgeSet)
    (hcard : 2*k=Fintype.card S)
    (hinc : (∑ i, (p i).toSubgraph.verts.ncard)=(k-1)*Fintype.card S)
    (x y : Fin k → V)
    (A : ∀ i, G.Walk (x i) (a i).val) (B : ∀ i, G.Walk (b i).val (y i))
    (hAp : ∀ i, (A i).IsPath) (hBp : ∀ i, (B i).IsPath)
    (hA : ∀ i, ∀ v ∈ (A i).support, v ∈ S → v=(a i).val)
    (hB : ∀ i, ∀ v ∈ (B i).support, v ∈ S → v=(b i).val)
    (hAB : ∀ i, ∀ v ∈ (A i).support, v ∈ (B i).support → False)
    (hdis : Pairwise (fun z w : Fin k × Bool ↦
      Disjoint (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)
        (if w.2 then (A w.1).toSubgraph.edgeSet else (B w.1).toSubgraph.edgeSet)))
    (hcover : (BridgeGlue.within G S).edgeSet ∪
      (⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet)=G.edgeSet) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  obtain ⟨htop,he⟩ := cycle_piece_incidence_saturation C hC hspan a b p hp hd hCp hc hcard hinc
  have hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v := by
    intro u hu v hv huv
    change (G.induce S).Adj (⟨u,hu⟩ : S) (⟨v,hv⟩ : S)
    rw [htop]
    exact fun he ↦ huv (congrArg Subtype.val he)
  obtain ⟨q,hq,hqd,hqc⟩ := splice_clique_pairs S a b x y A B he hclique
    hAp hBp hA hB hAB hdis hcover
  let U : TrailFamily G k :=
    { start := x
      finish := y
      walk := q
      isTrail := fun i ↦ (hq i).isTrail
      disjoint := hqd
      cover := fun e ↦ by rw [←hqc]; exact Set.mem_iUnion }
  exact MatchingAppend.path_family_partition U hq

end Erdos583SaturatedCycleCoreDevelopment
