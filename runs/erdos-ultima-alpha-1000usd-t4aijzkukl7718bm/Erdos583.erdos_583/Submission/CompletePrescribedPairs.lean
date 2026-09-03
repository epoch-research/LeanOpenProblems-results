import Submission.Work

/-! Complete even graphs admit indexed path partitions with any prescribed
perfect matching of their endpoints. Relabel an all-odd normal partition. -/
namespace Erdos583CompletePrescribedPairsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TrailNormalization Erdos583Work.NormalTrailSystem
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

/-- At the sharp all-odd budget, even an arbitrary trail family has each
vertex as an endpoint exactly once. -/
lemma sharp_odd_endpoint_bijective {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (T : QuotaTrails.TrailFamily G k)
    (hcard : 2*k=Fintype.card V)
    (ho : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then T.start z.1 else T.finish z.1) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro v
    have hq := (QuotaParity.quota_odd_iff T v).mpr (ho v)
    obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T hq.pos
    rcases hi with hi | hi
    · exact ⟨(i,true),by simpa using hi.symm⟩
    · exact ⟨(i,false),by simpa using hi.symm⟩
  · simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hcard

lemma complete_even_degree_odd {V : Type*} [Fintype V] {k : ℕ}
    (hcard : 2*k=Fintype.card V) (v : V) :
    Odd (Nat.card ((⊤ : SimpleGraph V).neighborSet v)) := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  change Odd ((completeGraph V).degree v)
  rw [complete_graph_degree,←hcard]
  exact ⟨k-1,by omega⟩

lemma cycle_remainder_endpoint_bijective {V : Type*} [Fintype V] {k : ℕ} {r : V}
    (C : (⊤ : SimpleGraph V).Walk r r) (hC : C.IsCycle)
    (T : QuotaTrails.TrailFamily ((⊤ : SimpleGraph V).deleteEdges C.toSubgraph.edgeSet) k)
    (hcard : 2*k=Fintype.card V) :
    Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then T.start z.1 else T.finish z.1) := by
  apply sharp_odd_endpoint_bijective T hcard
  intro v
  have ho := complete_even_degree_odd hcard v
  rw [Nat.card_coe_set_eq,Nat.odd_iff] at ho ⊢
  exact (delete_cycle_preserves_degree_parity hC v).trans ho

lemma complete_prescribed_pairs {V : Type*} [Fintype V] {k : ℕ}
    (a b : Fin k → V)
    (he : Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1)) :
    ∃ p : ∀ i, (⊤ : SimpleGraph V).Walk (a i) (b i),
      (∀ i, (p i).IsPath) ∧
      Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) ∧
      (⋃ i, (p i).toSubgraph.edgeSet)=(⊤ : SimpleGraph V).edgeSet := by
  classical
  have hcard : 2*k=Fintype.card V := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm]
      using Fintype.card_of_bijective he
  have ho (v : V) : Odd ((⊤ : SimpleGraph V).degree v) := by
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    change Odd ((completeGraph V).degree v)
    rw [complete_graph_degree, ←hcard]
    exact ⟨k-1,by omega⟩
  obtain ⟨l,hl,⟨T⟩⟩ := all_odd_normal_trail_system (⊤ : SimpleGraph V) ho
  have hlk : l=k := by omega
  subst l
  obtain ⟨U,hU⟩ := T.exists_max_score
  let d : Fin k × Bool ≃ V := Equiv.ofBijective _ he
  let e : V ≃ V := U.endpointEquiv.symm.trans d
  let f : (⊤ : SimpleGraph V) →g (⊤ : SimpleGraph V) :=
    ⟨e,fun h hn ↦ h (e.injective hn)⟩
  have ha (i : Fin k) : e (U.start i)=a i := by
    change d (U.endpointEquiv.symm (U.start i))=a i
    rw [show U.start i=U.endpointEquiv (i,true) from rfl, Equiv.symm_apply_apply]
    rfl
  have hb (i : Fin k) : e (U.finish i)=b i := by
    change d (U.endpointEquiv.symm (U.finish i))=b i
    rw [show U.finish i=U.endpointEquiv (i,false) from rfl, Equiv.symm_apply_apply]
    rfl
  let p (i : Fin k) := ((U.walk i).map f).copy (ha i) (hb i)
  have hp (i : Fin k) : (p i).IsPath := by
    simpa only [p,Walk.isPath_copy] using Walk.map_isPath_of_injective (f := f) e.injective (max_score_isPath U hU i)
  have hpe (i : Fin k) : (p i).toSubgraph.edgeSet=
      Sym2.map e '' (U.walk i).toSubgraph.edgeSet := by
    simp only [p,NormalTrailSystem.walk_copy_subgraph,Walk.toSubgraph_map,Subgraph.edgeSet_map]
    rfl
  have hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) := by
    intro i j hij
    rw [hpe,hpe]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hxy := (Sym2.map.injective e.injective) (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp (U.disjoint hij) hx (hxy.symm ▸ hy)
  refine ⟨p,hp,hd,?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
    exact (p i).toSubgraph.edgeSet_subset hi
  · induction z using Sym2.ind with
    | h x y =>
      intro hxy
      have hold : s(e.symm x,e.symm y) ∈ (⊤ : SimpleGraph V).edgeSet := by
        intro hn
        exact hxy (e.symm.injective hn)
      obtain ⟨i,hi⟩ := (U.cover _).mp hold
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_⟩
      rw [hpe]
      exact ⟨_,hi,by simp⟩

lemma clique_prescribed_pairs {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} (a b : Fin k → S)
    (he : Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1))
    (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) :
    ∃ p : ∀ i, G.Walk (a i).val (b i).val,
      (∀ i, (p i).IsPath) ∧
      (∀ i, ∀ x ∈ (p i).support, x ∈ S) ∧
      Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) ∧
      (⋃ i, (p i).toSubgraph.edgeSet)=(BridgeGlue.within G S).edgeSet := by
  classical
  obtain ⟨q,hq,hd,hcover⟩ := complete_prescribed_pairs a b he
  let f : (⊤ : SimpleGraph S) →g G :=
    ⟨Subtype.val,fun {x y} h ↦ hclique x.val x.property y.val y.property
      (fun hh ↦ h (Subtype.ext hh))⟩
  let p (i : Fin k) := (q i).map f
  have hpe (i : Fin k) : (p i).toSubgraph.edgeSet=
      Sym2.map (Subtype.val : S → V) '' (q i).toSubgraph.edgeSet := by
    simp only [p,Walk.toSubgraph_map,Subgraph.edgeSet_map]
    rfl
  have hps (i : Fin k) : ∀ x ∈ (p i).support, x ∈ S := by
    intro x hx
    rw [Walk.support_map] at hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact y.property
  refine ⟨p,fun i ↦ Walk.map_isPath_of_injective Subtype.val_injective (hq i),hps,?_,?_⟩
  · intro i j hij
    rw [hpe,hpe,Set.disjoint_image_iff (Sym2.map.injective Subtype.val_injective)]
    exact hd hij
  · ext e
    constructor
    · intro he
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
      exact PentagonCarriers.subgraph_edges_within (p i).toSubgraph S
        (fun x hx ↦ hps i x ((p i).mem_verts_toSubgraph.mp hx)) hi
    · induction e using Sym2.ind with
      | h x y =>
        rintro ⟨hxy,hx,hy⟩
        have he' : s((⟨x,hx⟩ : S),(⟨y,hy⟩ : S)) ∈ (⊤ : SimpleGraph S).edgeSet := by
          intro hh
          exact hxy.ne (congrArg Subtype.val hh)
        rw [←hcover] at he'
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he'
        apply Set.mem_iUnion.mpr
        refine ⟨i,?_⟩
        rw [hpe]
        exact ⟨_,hi,rfl⟩

end Erdos583CompletePrescribedPairsDevelopment
