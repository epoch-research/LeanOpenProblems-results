import Submission.PathCoreIntervals
import Submission.SaturatedCycleCore

/-! A complete even cycle core can absorb a cycle when every remaining
path meets the core in a single interval. The exterior arms are extracted
from the original simple paths, rather than assumed compatible. -/
namespace Erdos583CoreIntervalSplicingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.BridgeGlue
open Erdos583PathCoreIntervalsDevelopment Erdos583SaturatedCycleCoreDevelopment
open Erdos583CompleteCoreSplicingDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma induce_edge_iff {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (S : Set V) (hS : ∀ x ∈ P.support, x ∈ S)
    (e : Sym2 S) :
    e ∈ (P.induce S hS).toSubgraph.edgeSet ↔
      Sym2.map Subtype.val e ∈ P.toSubgraph.edgeSet := by
  have he : P.toSubgraph.edgeSet = Sym2.map Subtype.val ''
      (P.induce S hS).toSubgraph.edgeSet := by
    conv_lhs => rw [←Walk.map_induce P hS,Walk.toSubgraph_map,Subgraph.edgeSet_map]
    rfl
  rw [he,Set.mem_image]
  exact ⟨fun h ↦ ⟨e,h,rfl⟩,fun ⟨d,hd,hde⟩ ↦
    (Sym2.map.injective Subtype.val_injective hde) ▸ hd⟩

lemma clique_cycle_ports {V : Type*} [Fintype V] {H : SimpleGraph V}
    {k : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (a b : Fin k → V) (p : ∀ i, H.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsTrail)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=H.edgeSet)
    (hcard : 2*k=Fintype.card V) (htop : H=⊤) :
    Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1) := by
  have hdis : Disjoint C.toSubgraph.edgeSet (⋃ i, (p i).toSubgraph.edgeSet) := by
    apply Set.disjoint_left.mpr
    intro e heC heP
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heP
    exact Set.disjoint_left.mp (hCp i) heC hi
  have hsize : H.edgeSet.ncard=(Fintype.card V).choose 2 := by
    rw [htop,Set.ncard_eq_toFinset_card']
    exact card_edgeFinset_top_eq_card_choose_two
  rw [←hc,Set.ncard_union_eq hdis,trail_edgeSet_ncard C hC.isTrail,
    Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hd,finsum_eq_sum_of_fintype] at hsize
  have hload : C.length+(∑ i, (p i).length)=(Fintype.card V).choose 2 := by
    simpa only [trail_edgeSet_ncard _ (hp _)] using hsize
  exact (cycle_piece_saturation C hC a b p hp hd hCp hc hcard hload).2

lemma explicit_core_interval_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (S : Set V) (hCS : C.toSubgraph.verts=S)
    (a b x y : Fin k → V)
    (A : ∀ i, G.Walk (x i) (a i)) (Q : ∀ i, G.Walk (a i) (b i))
    (B : ∀ i, G.Walk (b i) (y i))
    (hp : ∀ i, ((A i).append ((Q i).append (B i))).IsPath)
    (hQS : ∀ i, ∀ v ∈ (Q i).support, v ∈ S)
    (hA : ∀ i, ∀ v ∈ (A i).support, v ∈ S → v=a i)
    (hB : ∀ i, ∀ v ∈ (B i).support, v ∈ S → v=b i)
    (hd : Pairwise (fun i j ↦
      Disjoint ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet
        ((A j).append ((Q j).append (B j))).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪
      (⋃ i, ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet)=G.edgeSet)
    (hcard : 2*k=Fintype.card S) (htop : G.induce S=⊤) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  have hCin : ∀ v ∈ C.support, v ∈ S := by
    intro v hv; rw [←hCS]; exact C.mem_verts_toSubgraph.mpr hv
  let c := C.induce S hCin
  let aa (i : Fin k) : S := ⟨a i,hQS i _ (Q i).start_mem_support⟩
  let bb (i : Fin k) : S := ⟨b i,hQS i _ (Q i).end_mem_support⟩
  let q (i : Fin k) : (G.induce S).Walk (aa i) (bb i) := (Q i).induce S (hQS i)
  have hcC : c.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective (f := (Embedding.induce S).toHom) Subtype.val_injective).mp
    simpa only [c,Walk.map_induce] using hC
  have hqp (i : Fin k) : (q i).IsPath := by
    apply Walk.IsPath.of_map (f := (Embedding.induce S).toHom)
    simpa only [q,Walk.map_induce] using (hp i).of_append_right.of_append_left
  have hqe (i : Fin k) : (Q i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet :=
    PentagonCarriers.middle_edges_subset _ _ _
  have hqd : Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp (hd hij)
      (hqe i ((induce_edge_iff (Q i) S (hQS i) e).mp he))
      (hqe j ((induce_edge_iff (Q j) S (hQS j) e).mp hf))
  have hcq (i : Fin k) : Disjoint c.toSubgraph.edgeSet (q i).toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp (hCp i) ((induce_edge_iff C S hCin e).mp he)
      (hqe i ((induce_edge_iff (Q i) S (hQS i) e).mp hf))
  have hcc : c.toSubgraph.edgeSet ∪ (⋃ i, (q i).toSubgraph.edgeSet)=(G.induce S).edgeSet := by
    ext e
    constructor
    · rintro (he | he)
      · exact c.toSubgraph.edgeSet_subset he
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
        exact (q i).toSubgraph.edgeSet_subset hi
    · induction e using Sym2.ind with
      | h u v =>
        intro he
        have heG : s(u.val,v.val) ∈ G.edgeSet := he
        rw [←hc] at heG
        rcases heG with heC | heP
        · exact Or.inl ((induce_edge_iff C S hCin _).mpr heC)
        · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heP
          apply Or.inr
          apply Set.mem_iUnion.mpr
          refine ⟨i,(induce_edge_iff (Q i) S (hQS i) _).mpr ?_⟩
          exact HeptagonCore.middle_adj_of_inside (A i) (Q i) (B i) S (hA i) (hB i)
            u.property v.property hi
  have he := clique_cycle_ports c hcC aa bb q (fun i ↦ (hqp i).isTrail) hqd hcq hcc hcard htop
  have hab (i : Fin k) : a i ≠ b i := by
    intro hab
    have hports : (if true then aa i else bb i)=(if false then aa i else bb i) :=
      Subtype.ext hab
    have hh := he.injective (a₁ := (i,true)) (a₂ := (i,false)) hports
    cases congrArg Prod.snd hh
  have hAB (i : Fin k) : ∀ v ∈ (A i).support, v ∈ (B i).support → False := by
    intro v hvA hvB
    by_cases hva : v=a i
    · subst v
      exact hab i (hB i _ hvB (hQS i _ (Q i).start_mem_support))
    · exact (hp i).ne_of_mem_support_of_append hva hvA
        (((Q i).mem_support_append_iff (B i)).mpr (Or.inr hvB)) rfl
  have hAe (i : Fin k) : (A i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hBe (i : Fin k) : (B i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_of_subset_right Set.subset_union_right _
  have hdis : Pairwise (fun z w : Fin k × Bool ↦
      Disjoint (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)
        (if w.2 then (A w.1).toSubgraph.edgeSet else (B w.1).toSubgraph.edgeSet)) := by
    rintro ⟨i,bi⟩ ⟨j,bj⟩ hij
    have hi : (if bi then (A i).toSubgraph.edgeSet else (B i).toSubgraph.edgeSet) ⊆
        ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
      cases bi <;> simp only [Bool.false_eq_true,if_false,if_true] <;> first | exact hAe i | exact hBe i
    have hj : (if bj then (A j).toSubgraph.edgeSet else (B j).toSubgraph.edgeSet) ⊆
        ((A j).append ((Q j).append (B j))).toSubgraph.edgeSet := by
      cases bj <;> simp only [Bool.false_eq_true,if_false,if_true] <;> first | exact hAe j | exact hBe j
    by_cases hij' : i=j
    · subst j
      have hab' : Disjoint (A i).toSubgraph.edgeSet (B i).toSubgraph.edgeSet := by
        apply Set.disjoint_left.mpr
        intro e hA' hB'
        induction e using Sym2.ind with
        | h u v =>
          exact hAB i u (Walk.mem_support_of_adj_toSubgraph hA')
            (Walk.mem_support_of_adj_toSubgraph hB')
      cases bi <;> cases bj
      · exact (hij rfl).elim
      · exact hab'.symm
      · exact hab'
      · exact (hij rfl).elim
    · exact (hd hij').mono hi hj
  have hcover : (within G S).edgeSet ∪
      (⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet)=G.edgeSet := by
    apply Set.Subset.antisymm
    · rintro e (he | he)
      · exact edgeSet_mono (within_le _ _) he
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
        exact hi.elim (fun h ↦ (A i).toSubgraph.edgeSet_subset h) (fun h ↦ (B i).toSubgraph.edgeSet_subset h)
    · intro e he
      rw [←hc] at he
      rcases he with heC | heP
      · exact Or.inl (PentagonCarriers.subgraph_edges_within C.toSubgraph S hCS.subset heC)
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heP
        simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup,Set.mem_union] at hi
        rcases hi with hiA | hiQ | hiB
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl hiA⟩)
        · apply Or.inl
          exact PentagonCarriers.subgraph_edges_within (Q i).toSubgraph S
            (fun _ h ↦ hQS i _ ((Q i).mem_verts_toSubgraph.mp h)) hiQ
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inr hiB⟩)
  have hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v := by
    intro u hu v hv huv
    change (G.induce S).Adj ⟨u,hu⟩ ⟨v,hv⟩
    rw [htop]
    exact fun h ↦ huv (congrArg Subtype.val h)
  obtain ⟨p,hp',hd',hc'⟩ := splice_clique_pairs S aa bb x y A B he hclique
    (fun i ↦ (hp i).of_append_left) (fun i ↦ (hp i).of_append_right.of_append_right)
    hA hB hAB hdis hcover
  let U : TrailFamily G k :=
    { start := x
      finish := y
      walk := p
      isTrail := fun i ↦ (hp' i).isTrail
      disjoint := hd'
      cover := fun e ↦ by rw [←hc']; exact Set.mem_iUnion }
  exact MatchingAppend.path_family_partition U hp'

/-- Numeric zero intrinsic deficit supplies all the interval and arm data. -/
lemma contiguous_clique_cycle_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin k → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, (coreVerts (p i) C.toSubgraph.verts).Nonempty)
    (hz : ∀ i, (coreEdges (p i) C.toSubgraph.verts).ncard+1=
      (coreVerts (p i) C.toSubgraph.verts).ncard)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*k) (htop : G.induce C.toSubgraph.verts=⊤) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  choose u v A Q B hform hQ hQv hA hB using
    fun i ↦ contiguous_of_core_count (p i) (hp i) C.toSubgraph.verts (hS i) (hz i)
  have hcard : 2*k=Fintype.card C.toSubgraph.verts := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Walk.verts_toSubgraph,
      cycle_support_ncard hC,hlen]
  apply explicit_core_interval_splice C hC C.toSubgraph.verts rfl u v a b A Q B
    (fun i ↦ hform i ▸ hp i) ?_ hA hB ?_ ?_ ?_ hcard htop
  · intro i x hx
    have hmem := (Q i).mem_verts_toSubgraph.mpr hx
    rw [hQv i] at hmem
    exact hmem.2
  · simpa only [←hform] using hd
  · simpa only [←hform] using hCp
  · simpa only [←hform] using hc

end Erdos583CoreIntervalSplicingDevelopment
