import Submission.CoreIntervalSplicing
import Submission.NearCompleteCoreSplicing

/-! Unbounded-length absorption for a near-complete even cycle core whose
carriers each have a contiguous intersection with the core. -/
namespace Erdos583NearCompleteContiguousAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.BridgeGlue
open Erdos583PathCoreIntervalsDevelopment Erdos583CoreIntervalSplicingDevelopment
open Erdos583NearCompleteCorePortsDevelopment Erdos583NearCompleteCoreSplicingDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma explicit_near_complete_interval_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (S : Set V) (hCS : C.toSubgraph.verts=S)
    (a b x y : Fin t → V)
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
    (hcard : 2*t+2=Fintype.card S) (u₀ v₀ : S) (huv₀ : u₀ ≠ v₀)
    (hnear : G.induce S=(⊤ : SimpleGraph S).deleteEdges {s(u₀,v₀)}) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  have hCin : ∀ v ∈ C.support, v ∈ S := by
    intro v hv; rw [←hCS]; exact C.mem_verts_toSubgraph.mpr hv
  let c := C.induce S hCin
  let aa (i : Fin t) : S := ⟨a i,hQS i _ (Q i).start_mem_support⟩
  let bb (i : Fin t) : S := ⟨b i,hQS i _ (Q i).end_mem_support⟩
  let q (i : Fin t) : (G.induce S).Walk (aa i) (bb i) := (Q i).induce S (hQS i)
  have hcC : c.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective (f := (Embedding.induce S).toHom) Subtype.val_injective).mp
    simpa only [c,Walk.map_induce] using hC
  have hqp (i : Fin t) : (q i).IsPath := by
    apply Walk.IsPath.of_map (f := (Embedding.induce S).toHom)
    simpa only [q,Walk.map_induce] using (hp i).of_append_right.of_append_left
  have hqe (i : Fin t) : (Q i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet :=
    PentagonCarriers.middle_edges_subset _ _ _
  have hqd : Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp (hd hij)
      (hqe i ((induce_edge_iff (Q i) S (hQS i) e).mp he))
      (hqe j ((induce_edge_iff (Q j) S (hQS j) e).mp hf))
  have hcq (i : Fin t) : Disjoint c.toSubgraph.edgeSet (q i).toSubgraph.edgeSet := by
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
  have he := near_complete_cycle_ports c hcC aa bb q (fun i ↦ (hqp i).isTrail) hqd hcq hcc u₀ v₀ hcard hnear
  have hab (i : Fin t) : a i ≠ b i := by
    intro hab
    have hports : (if true then aa i else bb i)=(if false then aa i else bb i) :=
      Subtype.ext hab
    have hh := he.injective (a₁ := Sum.inl (i,true)) (a₂ := Sum.inl (i,false)) hports
    cases congrArg Prod.snd (Sum.inl.inj hh)
  have hAB (i : Fin t) : ∀ v ∈ (A i).support, v ∈ (B i).support → False := by
    intro v hvA hvB
    by_cases hva : v=a i
    · subst v
      exact hab i (hB i _ hvB (hQS i _ (Q i).start_mem_support))
    · exact (hp i).ne_of_mem_support_of_append hva hvA
        (((Q i).mem_support_append_iff (B i)).mpr (Or.inr hvB)) rfl
  have hAe (i : Fin t) : (A i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hBe (i : Fin t) : (B i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_of_subset_right Set.subset_union_right _
  have hdis : Pairwise (fun z w : Fin t × Bool ↦
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
  have ht : 0 < t := by
    have hv : Fintype.card S=C.length := by
      rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,←hCS,Walk.verts_toSubgraph,
        cycle_support_ncard hC]
    have h3 := hC.three_le_length
    omega
  exact splice_near_complete_fresh_pair S aa bb u₀ v₀ huv₀ ⟨0,ht⟩ hnear he x y A B
    (fun i ↦ (hp i).of_append_left) (fun i ↦ (hp i).of_append_right.of_append_right)
    hA hB hAB hdis hcover

/-- The complete-minus-one-edge cycle core absorbs itself into the carriers
with one extra slot when each carrier meets the core in a single interval.
No vertex-disjointness between different exterior arms is assumed. -/
lemma contiguous_near_complete_cycle_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, (coreVerts (p i) C.toSubgraph.verts).Nonempty)
    (hz : ∀ i, (coreEdges (p i) C.toSubgraph.verts).ncard+1=
      (coreVerts (p i) C.toSubgraph.verts).ncard)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (u₀ v₀ : C.toSubgraph.verts) (huv₀ : u₀ ≠ v₀)
    (hnear : G.induce C.toSubgraph.verts=
      (⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u₀,v₀)}) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  choose u v A Q B hform hQ hQv hA hB using
    fun i ↦ contiguous_of_core_count (p i) (hp i) C.toSubgraph.verts (hS i) (hz i)
  have hcard : 2*t+2=Fintype.card C.toSubgraph.verts := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Walk.verts_toSubgraph,
      cycle_support_ncard hC,hlen]
  apply explicit_near_complete_interval_splice C hC C.toSubgraph.verts rfl u v a b A Q B
    (fun i ↦ hform i ▸ hp i) ?_ hA hB ?_ ?_ ?_ hcard u₀ v₀ huv₀ hnear
  · intro i x hx
    have hmem := (Q i).mem_verts_toSubgraph.mpr hx
    rw [hQv i] at hmem
    exact hmem.2
  · simpa only [←hform] using hd
  · simpa only [←hform] using hCp
  · simpa only [←hform] using hc

end Erdos583NearCompleteContiguousAbsorptionDevelopment
