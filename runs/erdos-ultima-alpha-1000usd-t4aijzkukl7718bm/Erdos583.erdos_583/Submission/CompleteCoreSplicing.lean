import Submission.CompletePrescribedPairs

/-! Splicing arbitrary compatible exterior arms through a complete even core.
Only paired arms must avoid each other; different output paths may intersect. -/
namespace Erdos583CompleteCoreSplicingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CompletePrescribedPairsDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma splice_clique_pairs {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} (a b : Fin k → S) (x y : Fin k → V)
    (A : ∀ i, G.Walk (x i) (a i).val) (B : ∀ i, G.Walk (b i).val (y i))
    (he : Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1))
    (hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
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
  obtain ⟨Q,hQ,hQS,hQQ,hQc⟩ := clique_prescribed_pairs S a b he hclique
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

/-- When the old core pieces form a sharp trail partition after deleting a
cycle from a complete even core, their endpoint ports are automatically
bijective. The cycle can then be absorbed while preserving those pairings. -/
lemma clique_cycle_remainder_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} {r : S}
    (C : (⊤ : SimpleGraph S).Walk r r) (hC : C.IsCycle)
    (T : TrailFamily ((⊤ : SimpleGraph S).deleteEdges C.toSubgraph.edgeSet) k)
    (hcard : 2*k=Fintype.card S) (x y : Fin k → V)
    (A : ∀ i, G.Walk (x i) (T.start i).val)
    (B : ∀ i, G.Walk (T.finish i).val (y i))
    (hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
    (hAp : ∀ i, (A i).IsPath) (hBp : ∀ i, (B i).IsPath)
    (hA : ∀ i, ∀ v ∈ (A i).support, v ∈ S → v=(T.start i).val)
    (hB : ∀ i, ∀ v ∈ (B i).support, v ∈ S → v=(T.finish i).val)
    (hAB : ∀ i, ∀ v ∈ (A i).support, v ∈ (B i).support → False)
    (hdis : Pairwise (fun z w : Fin k × Bool ↦
      Disjoint (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)
        (if w.2 then (A w.1).toSubgraph.edgeSet else (B w.1).toSubgraph.edgeSet)))
    (hcover : (BridgeGlue.within G S).edgeSet ∪
      (⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet)=G.edgeSet) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  obtain ⟨p,hp,hd,hc⟩ := splice_clique_pairs S T.start T.finish x y A B
    (cycle_remainder_endpoint_bijective C hC T hcard) hclique hAp hBp hA hB hAB hdis hcover
  let U : TrailFamily G k :=
    { start := x
      finish := y
      walk := p
      isTrail := fun i ↦ (hp i).isTrail
      disjoint := hd
      cover := fun e ↦ by rw [←hc]; exact Set.mem_iUnion }
  exact MatchingAppend.path_family_partition U hp

end Erdos583CompleteCoreSplicingDevelopment
