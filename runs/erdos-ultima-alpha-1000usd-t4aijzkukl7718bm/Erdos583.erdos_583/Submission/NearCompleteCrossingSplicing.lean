import Submission.CoreIntervalSplicing
import Submission.NearCompleteIntervalCollision
import Submission.OneCollisionCrossing
import Submission.CorePairSplicing

/-! Near-complete core splicing allowing one nil interval. The nil interval
must have a partner whose same-side exterior arms are vertex-disjoint. -/
namespace Erdos583NearCompleteCrossingSplicingDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.BridgeGlue
open Erdos583PathCoreIntervalsDevelopment Erdos583CoreIntervalSplicingDevelopment
open Erdos583NearCompleteIntervalCollisionDevelopment Erdos583OneCollisionCrossingDevelopment Erdos583CorePairSplicingDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma explicit_near_complete_crossing_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
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
    (hcap : ∀ w ∈ S, (Finset.univ.filter fun i ↦ w ∈ (Q i).support).card ≤ t)
    (hcross : ∀ i, a i=b i → ∃ j, i ≠ j ∧
      Disjoint {w | w ∈ (A i).support} {w | w ∈ (A j).support} ∧
      Disjoint {w | w ∈ (B i).support} {w | w ∈ (B j).support}) :
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
  have hqcap (w : S) (_ : w ≠ u₀) (_ : w ≠ v₀) :
      (Finset.univ.filter fun i ↦ w ∈ (q i).support).card ≤ t := by
    have hm (i : Fin (t+1)) : w ∈ (q i).support ↔ w.val ∈ (Q i).support := by
      simp only [q,Walk.support_induce,List.mem_attachWith]
    simp_rw [hm]
    exact hcap w.val w.property
  obtain ⟨om,du,hod,_,e,_,_,he,_,hbij⟩ := near_complete_cycle_interval_collision c hcC aa bb q hqp
    hqd hcq hcc u₀ v₀ huv₀ hcard hnear (fun w hwu hwv ↦ by
      convert hqcap w hwu hwv using 1
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and])
  have hAB (i : Fin (t+1)) (hab : a i ≠ b i) :
      ∀ v ∈ (A i).support, v ∈ (B i).support → False := by
    intro v hvA hvB
    by_cases hva : v=a i
    · subst v
      exact hab (hB i _ hvB (hQS i _ (Q i).start_mem_support))
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
        apply (RootedTailSystem.append_trail_disjoint (hp i).isTrail).mono_right
        simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
        exact Set.subset_union_right
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
  let label (z : Fin (t+1) × Bool) : S := if z.2 then aa z.1 else bb z.1
  let outer (z : Fin (t+1) × Bool) : V := if z.2 then x z.1 else y z.1
  let arm : ∀ z, G.Walk (outer z) (label z).val := fun ⟨i,c⟩ ↦
    match c with
    | true => A i
    | false => (B i).reverse
  have harme (z : Fin (t+1) × Bool) : (arm z).toSubgraph.edgeSet=
      if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet := by
    rcases z with ⟨i,c⟩
    cases c <;> simp only [arm,Walk.toSubgraph_reverse,Bool.false_eq_true,if_false,if_true]
  have harmp (z : Fin (t+1) × Bool) : (arm z).IsPath := by
    rcases z with ⟨i,c⟩
    cases c
    · exact (hp i).of_append_right.of_append_right.reverse
    · exact (hp i).of_append_left
  have harmS (z : Fin (t+1) × Bool) : ∀ w ∈ (arm z).support, w ∈ S → w=(label z).val := by
    rcases z with ⟨i,c⟩
    cases c
    · simpa only [arm,Walk.support_reverse,List.mem_reverse] using hB i
    · exact hA i
  have harmd : Pairwise (fun z w ↦ Disjoint (arm z).toSubgraph.edgeSet (arm w).toSubgraph.edgeSet) := by
    simpa only [harme] using hdis
  have harmc : (within G S).edgeSet ∪ (⋃ z, (arm z).toSubgraph.edgeSet)=G.edgeSet := by
    rw [←hcover]
    congr 1
    ext e
    simp only [Set.mem_iUnion,Set.mem_union,harme]
    constructor
    · rintro ⟨⟨i,c⟩,hi⟩
      refine ⟨i,?_⟩
      cases c
      · exact Or.inr hi
      · exact Or.inl hi
    · rintro ⟨i,hi | hi⟩
      · exact ⟨(i,true),hi⟩
      · exact ⟨(i,false),hi⟩
  have harmcompat (i : Fin (t+1)) (hi : label (i,true) ≠ label (i,false)) :
      Disjoint {w | w ∈ (arm (i,true)).support} {w | w ∈ (arm (i,false)).support} := by
    apply Set.disjoint_left.mpr
    intro w hwA hwB
    exact hAB i (fun h ↦ hi (Subtype.ext h)) w hwA
      (by simpa only [arm,Walk.support_reverse,List.mem_reverse] using hwB)
  have harmcross (hi : label (e.1,true)=label (e.1,false)) : ∃ j, e.1 ≠ j ∧
      Disjoint {w | w ∈ (arm (e.1,true)).support} {w | w ∈ (arm (j,true)).support} ∧
      Disjoint {w | w ∈ (arm (e.1,false)).support} {w | w ∈ (arm (j,false)).support} := by
    obtain ⟨j,hej,hAA,hBB⟩ := hcross e.1 (congrArg Subtype.val hi)
    exact ⟨j,hej,hAA,by simpa only [arm,Walk.support_reverse,List.mem_reverse] using hBB⟩
  have hne : om ≠ du := by rcases hod with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩; exact huv₀; exact huv₀.symm
  have hnear' : G.induce S=(⊤ : SimpleGraph S).deleteEdges {s(om,du)} := by
    rcases hod with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hnear
    · simpa only [Sym2.eq_swap] using hnear
  exact near_complete_splice_one_collision S label outer arm harmp harmS harmd harmc
    om du hne hnear' e he hbij harmcompat harmcross

end Erdos583NearCompleteCrossingSplicingDevelopment
