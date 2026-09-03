import Submission.CoreIntervalSplicing
import Submission.NearCompleteIntervalPairs
import Submission.CorePairSplicing

/-! Absorbing a near-complete even core without adding further slots,
when the nonnil core intervals satisfy the sharp vertex-incidence bound. -/
namespace Erdos583NearCompleteCapacitySplicingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.BridgeGlue
open Erdos583PathCoreIntervalsDevelopment Erdos583CoreIntervalSplicingDevelopment
open Erdos583NearCompleteIntervalPairsDevelopment Erdos583CorePairSplicingDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma explicit_near_complete_capacity_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (S : Set V) (hCS : C.toSubgraph.verts=S)
    (a b x y : Fin (t+1) → V)
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
    (hnear : G.induce S=(⊤ : SimpleGraph S).deleteEdges {s(u₀,v₀)})
    (hab : ∀ i, a i ≠ b i)
    (hcap : ∀ w ∈ S, (Finset.univ.filter fun i ↦ w ∈ (Q i).support).card ≤ t) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  have hCin : ∀ v ∈ C.support, v ∈ S := by
    intro v hv; rw [←hCS]; exact C.mem_verts_toSubgraph.mpr hv
  let c := C.induce S hCin
  let aa (i : Fin (t+1)) : S := ⟨a i,hQS i _ (Q i).start_mem_support⟩
  let bb (i : Fin (t+1)) : S := ⟨b i,hQS i _ (Q i).end_mem_support⟩
  let q (i : Fin (t+1)) : (G.induce S).Walk (aa i) (bb i) := (Q i).induce S (hQS i)
  have hcC : c.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective (f := (Embedding.induce S).toHom) Subtype.val_injective).mp
    simpa only [c,Walk.map_induce] using hC
  have hqp (i : Fin (t+1)) : (q i).IsPath := by
    apply Walk.IsPath.of_map (f := (Embedding.induce S).toHom)
    simpa only [q,Walk.map_induce] using (hp i).of_append_right.of_append_left
  have hqe (i : Fin (t+1)) : (Q i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet :=
    PentagonCarriers.middle_edges_subset _ _ _
  have hqd : Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp (hd hij)
      (hqe i ((induce_edge_iff (Q i) S (hQS i) e).mp he))
      (hqe j ((induce_edge_iff (Q j) S (hQS j) e).mp hf))
  have hcq (i : Fin (t+1)) : Disjoint c.toSubgraph.edgeSet (q i).toSubgraph.edgeSet := by
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
  have hab' (i : Fin (t+1)) : aa i ≠ bb i := fun h ↦ hab i (congrArg Subtype.val h)
  have hqcap (w : S) (_ : w ≠ u₀) (_ : w ≠ v₀) :
      (Finset.univ.filter fun i ↦ w ∈ (q i).support).card ≤ t := by
    have hm (i : Fin (t+1)) : w ∈ (q i).support ↔ w.val ∈ (Q i).support := by
      simp only [q,Walk.support_induce,List.mem_attachWith]
    simp_rw [hm]
    exact hcap w.val w.property
  obtain ⟨core,hcore,hcored,hcorec⟩ := near_complete_interval_pairs c hcC aa bb q hqp hab'
    hqd hcq hcc u₀ v₀ huv₀ hcard hnear (fun w hwu hwv ↦ by
      convert hqcap w hwu hwv using 1
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and])
  obtain ⟨Q',hQ',hQ'S,hQ'd,hQ'c⟩ := map_induced_partition S aa bb core hcore hcored hcorec
  have hAB (i : Fin (t+1)) : ∀ v ∈ (A i).support, v ∈ (B i).support → False := by
    intro v hvA hvB
    by_cases hva : v=a i
    · subst v
      exact hab i (hB i _ hvB (hQS i _ (Q i).start_mem_support))
    · exact (hp i).ne_of_mem_support_of_append hva hvA
        (((Q i).mem_support_append_iff (B i)).mpr (Or.inr hvB)) rfl
  have hAe (i : Fin (t+1)) : (A i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hBe (i : Fin (t+1)) : (B i).toSubgraph.edgeSet ⊆
      ((A i).append ((Q i).append (B i))).toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_of_subset_right Set.subset_union_right _
  have hdis : Pairwise (fun z w : Fin (t+1) × Bool ↦
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
  obtain ⟨p,hp',hd',hc'⟩ := splice_given_core_pairs S aa bb x y A B Q' hQ' hQ'S hQ'd hQ'c
    (fun i ↦ (hp i).of_append_left) (fun i ↦ (hp i).of_append_right.of_append_right)
    hA hB hAB hdis hcover
  let U : TrailFamily G (t+1) :=
    { start := x
      finish := y
      walk := p
      isTrail := fun i ↦ (hp' i).isTrail
      disjoint := hd'
      cover := fun e ↦ by rw [←hc']; exact Set.mem_iUnion }
  exact MatchingAppend.path_family_partition U hp'

lemma path_ends_ne_of_two_vertices {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (hp : P.IsPath) (hn : 2 ≤ P.toSubgraph.verts.ncard) : a ≠ b := by
  intro hab
  subst b
  have hnil := (Walk.isPath_iff_eq_nil P).mp hp
  simp [hnil] at hn

lemma contiguous_near_complete_capacity_absorption {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin (t+1) → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, 2 ≤ (coreVerts (p i) C.toSubgraph.verts).ncard)
    (hz : ∀ i, (coreEdges (p i) C.toSubgraph.verts).ncard+1=
      (coreVerts (p i) C.toSubgraph.verts).ncard)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (u₀ v₀ : C.toSubgraph.verts) (huv₀ : u₀ ≠ v₀)
    (hnear : G.induce C.toSubgraph.verts=
      (⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u₀,v₀)})
    (hcap : ∀ w ∈ C.toSubgraph.verts,
      (Finset.univ.filter fun i ↦ w ∈ (p i).support).card ≤ t) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ t+1 := by
  classical
  have hne (i : Fin (t+1)) : (coreVerts (p i) C.toSubgraph.verts).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by have := hS i; omega)
  choose u v A Q B hform hQ hQv hA hB using
    fun i ↦ contiguous_of_core_count (p i) (hp i) C.toSubgraph.verts (hne i) (hz i)
  have hcard : 2*t+2=Fintype.card C.toSubgraph.verts := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Walk.verts_toSubgraph,
      cycle_support_ncard hC,hlen]
  apply explicit_near_complete_capacity_splice C hC C.toSubgraph.verts rfl u v a b A Q B
    (fun i ↦ hform i ▸ hp i) ?_ hA hB ?_ ?_ ?_ hcard u₀ v₀ huv₀ hnear ?_ ?_
  · intro i x hx
    have hmem := (Q i).mem_verts_toSubgraph.mpr hx
    rw [hQv i] at hmem
    exact hmem.2
  · simpa only [←hform] using hd
  · simpa only [←hform] using hCp
  · simpa only [←hform] using hc
  · intro i
    apply path_ends_ne_of_two_vertices (Q i) (hQ i)
    rw [hQv i]
    exact hS i
  · intro w hw
    apply le_trans (Finset.card_le_card (show
      (Finset.univ.filter fun i ↦ w ∈ (Q i).support) ⊆
        (Finset.univ.filter fun i ↦ w ∈ (p i).support) from ?_)) (hcap w hw)
    intro i hi
    obtain ⟨_,hi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hm := (Q i).mem_verts_toSubgraph.mpr hi
    rw [hQv i] at hm
    exact (p i).mem_verts_toSubgraph.mp hm.1

end Erdos583NearCompleteCapacitySplicingDevelopment
