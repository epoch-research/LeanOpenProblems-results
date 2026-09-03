import Submission.CompleteCoreSplicing

/-! Generic splicing through a supplied path partition of an induced core. -/
namespace Erdos583CorePairSplicingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma splice_given_core_pairs {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} (a b : Fin k → S) (x y : Fin k → V)
    (A : ∀ i, G.Walk (x i) (a i).val) (B : ∀ i, G.Walk (b i).val (y i))
    (Q : ∀ i, G.Walk (a i).val (b i).val)
    (hQ : ∀ i, (Q i).IsPath)
    (hQS : ∀ i, ∀ v ∈ (Q i).support, v ∈ S)
    (hQQ : Pairwise (fun i j ↦ Disjoint (Q i).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet))
    (hQc : (⋃ i, (Q i).toSubgraph.edgeSet)=(BridgeGlue.within G S).edgeSet)
    (hAp : ∀ i, (A i).IsPath) (hBp : ∀ i, (B i).IsPath)
    (hA : ∀ i, ∀ v ∈ (A i).support, v ∈ S → v=(a i).val)
    (hB : ∀ i, ∀ v ∈ (B i).support, v ∈ S → v=(b i).val)
    (hAB : ∀ i, ∀ v ∈ (A i).support, v ∈ (B i).support → False)
    (hdis : Pairwise (fun z w : Fin k × Bool ↦
      Disjoint (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)
        (if w.2 then (A w.1).toSubgraph.edgeSet else (B w.1).toSubgraph.edgeSet)))
    (hcover : (BridgeGlue.within G S).edgeSet ∪
      (⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet)=G.edgeSet) :
    ∃ p : ∀ i, G.Walk (x i) (y i),
      (∀ i, (p i).IsPath) ∧
      Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) ∧
      (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet := by
  classical
  let p (i : Fin k) := (A i).append ((Q i).append (B i))
  have hp (i : Fin k) : (p i).IsPath := by
    have hQB : ((Q i).append (B i)).IsPath := path_append_of_support_intersection
      (hQ i) (hBp i) (fun v hvQ hvB ↦ hB i v hvB (hQS i v hvQ))
    apply path_append_of_support_intersection (hAp i) hQB
    intro v hvA hvQB
    rcases ((Q i).mem_support_append_iff (B i)).mp hvQB with hvQ | hvB
    · exact hA i v hvA (hQS i v hvQ)
    · exact (hAB i v hvA hvB).elim
  have hAQ (i j : Fin k) : Disjoint (A i).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet :=
    LollipopEar.edge_disjoint_of_one_common_vertex _ _ (fun v hvA hvQ ↦ hA i v hvA (hQS j v hvQ))
  have hBQ (i j : Fin k) : Disjoint (B i).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet :=
    LollipopEar.edge_disjoint_of_one_common_vertex _ _ (fun v hvB hvQ ↦ hB i v hvB (hQS j v hvQ))
  have hAA {i j : Fin k} (hij : i ≠ j) : Disjoint (A i).toSubgraph.edgeSet (A j).toSubgraph.edgeSet := by
    simpa using hdis (i := (i,true)) (j := (j,true)) (fun h ↦ hij (congrArg Prod.fst h))
  have hBB {i j : Fin k} (hij : i ≠ j) : Disjoint (B i).toSubgraph.edgeSet (B j).toSubgraph.edgeSet := by
    simpa using hdis (i := (i,false)) (j := (j,false)) (fun h ↦ hij (congrArg Prod.fst h))
  have hAB' (i j : Fin k) : Disjoint (A i).toSubgraph.edgeSet (B j).toSubgraph.edgeSet := by
    simpa using hdis (i := (i,true)) (j := (j,false)) (by intro h; cases congrArg Prod.snd h)
  have hpe (i : Fin k) : (p i).toSubgraph.edgeSet =
      (A i).toSubgraph.edgeSet ∪ ((Q i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet) := by
    simp only [p,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
  refine ⟨p,hp,?_,?_⟩
  · intro i j hij
    simp only [hpe,Set.disjoint_union_left,Set.disjoint_union_right]
    exact ⟨⟨hAA hij,(hAQ j i).symm,(hAB' j i).symm⟩,
      ⟨hAQ i j,hQQ hij,hBQ i j⟩,
      hAB' i j,(hBQ j i).symm,hBB hij⟩
  · ext e
    rw [←hcover,←hQc]
    simp only [Set.mem_iUnion,Set.mem_union,hpe]
    constructor
    · rintro ⟨i,hiA | hiQ | hiB⟩
      · exact Or.inr ⟨i,Or.inl hiA⟩
      · exact Or.inl ⟨i,hiQ⟩
      · exact Or.inr ⟨i,Or.inr hiB⟩
    · rintro (⟨i,hiQ⟩ | ⟨i,hiA | hiB⟩)
      · exact ⟨i,Or.inr (Or.inl hiQ)⟩
      · exact ⟨i,Or.inl hiA⟩
      · exact ⟨i,Or.inr (Or.inr hiB)⟩

lemma map_induced_partition {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} (a b : Fin k → S)
    (q : ∀ i, (G.induce S).Walk (a i) (b i))
    (hq : ∀ i, (q i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet))
    (hc : (⋃ i, (q i).toSubgraph.edgeSet)=(G.induce S).edgeSet) :
    ∃ p : ∀ i, G.Walk (a i).val (b i).val,
      (∀ i, (p i).IsPath) ∧
      (∀ i, ∀ x ∈ (p i).support, x ∈ S) ∧
      Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) ∧
      (⋃ i, (p i).toSubgraph.edgeSet)=(BridgeGlue.within G S).edgeSet := by
  let p (i : Fin k) := (q i).map (Embedding.induce S).toHom
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
        have he' : s((⟨x,hx⟩ : S),(⟨y,hy⟩ : S)) ∈ (G.induce S).edgeSet := hxy
        rw [←hc] at he'
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he'
        apply Set.mem_iUnion.mpr
        refine ⟨i,?_⟩
        rw [hpe]
        exact ⟨_,hi,rfl⟩

end Erdos583CorePairSplicingDevelopment
