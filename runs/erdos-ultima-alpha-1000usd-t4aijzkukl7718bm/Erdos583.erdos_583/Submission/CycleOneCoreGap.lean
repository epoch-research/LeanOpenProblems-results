import Submission.PathCoreIntervals
import Submission.OneGapArithmetic
import Submission.SaturatedCycleCore

/-! Deriving core saturation from at most one aggregate core-edge deficit.
The later reconstruction step must still provide compatible exterior arms. -/
namespace Erdos583CycleOneCoreGapDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.BridgeGlue
open Erdos583PathCoreIntervalsDevelopment Erdos583OneGapArithmeticDevelopment
open Erdos583SaturatedCycleCoreDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ} {r : V}

omit [Fintype V] in
lemma cycle_paths_inside_edges (C : G.Walk r r)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet) :
    C.toSubgraph.edgeSet ∪ (⋃ i, coreEdges (p i) C.toSubgraph.verts)=
      (within G C.toSubgraph.verts).edgeSet := by
  ext e
  constructor
  · rintro (he | he)
    · exact PentagonCarriers.subgraph_edges_within C.toSubgraph _ (Set.Subset.refl _) he
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
      exact hi.2
  · intro he
    have heG : e ∈ G.edgeSet := edgeSet_mono (within_le _ _) he
    rw [←hc] at heG
    rcases heG with heC | heP
    · exact Or.inl heC
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heP
      exact Or.inr (Set.mem_iUnion.mpr ⟨i,hi,he⟩)

lemma cycle_paths_inside_count (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet) :
    (within G C.toSubgraph.verts).edgeSet.ncard =
      C.length + ∑ i, (coreEdges (p i) C.toSubgraph.verts).ncard := by
  have he := cycle_paths_inside_edges C a b p hc
  have hdis : Disjoint C.toSubgraph.edgeSet (⋃ i, coreEdges (p i) C.toSubgraph.verts) := by
    apply Set.disjoint_left.mpr
    intro e heC heP
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heP
    exact Set.disjoint_left.mp (hCp i) heC hi.1
  have hdd : Pairwise (fun i j ↦ Disjoint (coreEdges (p i) C.toSubgraph.verts)
      (coreEdges (p j) C.toSubgraph.verts)) := by
    intro i j hij
    exact (hd hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [←he,Set.ncard_union_eq hdis,trail_edgeSet_ncard C hC.isTrail,
    Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hdd,finsum_eq_sum_of_fintype]

lemma one_core_gap_forces_clique (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hS : ∀ i, (coreVerts (p i) C.toSubgraph.verts).Nonempty)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hdense : C.length ≤ 2*t+2)
    (hgap : (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard)) ≤ 1) :
    C.length=2*t+2 ∧
      (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard))=1 ∧
      G.induce C.toSubgraph.verts=⊤ := by
  classical
  have hsize : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  have hupper (i : Fin t) : (coreEdges (p i) C.toSubgraph.verts).ncard ≤ C.length-1 := by
    have hb := core_edge_bound (p i) (hp i) C.toSubgraph.verts (hS i)
    have hv := Set.ncard_mono (show coreVerts (p i) C.toSubgraph.verts ⊆ C.toSubgraph.verts
      from Set.inter_subset_right)
    rw [hsize] at hv
    omega
  have hterm (i : Fin t) : (coreEdges (p i) C.toSubgraph.verts).ncard+
      (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard)=C.length-1 :=
    Nat.add_sub_of_le (hupper i)
  have hsum : (∑ i, (coreEdges (p i) C.toSubgraph.verts).ncard)+
      (∑ i, (C.length-1-(coreEdges (p i) C.toSubgraph.verts).ncard))=t*(C.length-1) := by
    rw [←Finset.sum_add_distrib]
    simp only [hterm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hcount := cycle_paths_inside_count C hC a b p hd hCp hc
  have hb := PentagonCarriers.within_edge_bound G C.toSubgraph.verts
  rw [hsize,hcount] at hb
  obtain ⟨hlen,hgap1,hfull⟩ := one_gap_arithmetic C.length t _ _ hC.three_le_length hdense hsum hgap hb
  refine ⟨hlen,hgap1,full_edge_count_eq_top (G.induce C.toSubgraph.verts) ?_⟩
  have hv : Fintype.card C.toSubgraph.verts=C.length := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,hsize]
  rw [←GlobalCritical.within_edge_ncard,hcount,hv]
  exact hfull

omit [Fintype V] in
/-- A vertex of degree greater than twice the number of path members cannot
be missed by any of them: the cycle supplies at most two incident edges. -/
lemma high_degree_on_every_path (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (x : V) (hx : 2*t < (G.neighborSet x).ncard) :
    ∀ i, x ∈ (p i).support := by
  classical
  intro j
  by_contra hj
  have hzero : (p j).toSubgraph.neighborSet x=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hj (Walk.mem_support_of_adj_toSubgraph hy)
  have hterm (i : Fin t) : ((p i).toSubgraph.neighborSet x).ncard+
      (if i=j then 2 else 0) ≤ 2 := by
    by_cases hi : i=j
    · subst i; simp [hzero]
    · simpa [hi] using path_neighbor_ncard_le_two ⟨a i,b i,p i,hp i,rfl⟩ x
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hterm i)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  have hn : G.neighborSet x=C.toSubgraph.neighborSet x ∪
      (⋃ i, (p i).toSubgraph.neighborSet x) := by
    ext y
    change s(x,y) ∈ G.edgeSet ↔ _
    rw [←hc]
    simp only [Set.mem_union,Set.mem_iUnion]
    rfl
  have hcy : (C.toSubgraph.neighborSet x).ncard ≤ 2 := by
    by_cases hxC : x ∈ C.support
    · exact (hC.ncard_neighborSet_toSubgraph_eq_two hxC).le
    · have he : C.toSubgraph.neighborSet x=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hxC (Walk.mem_support_of_adj_toSubgraph hy)
      simp [he]
  have hu := Set.ncard_union_le (C.toSubgraph.neighborSet x) (⋃ i, (p i).toSubgraph.neighborSet x)
  have hi := Set.ncard_iUnion_le_of_fintype (fun i ↦ (p i).toSubgraph.neighborSet x)
  rw [←hn] at hu
  omega

lemma spanning_of_complete_core (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (htop : G.induce C.toSubgraph.verts=⊤) :
    ∀ i, coreVerts (p i) C.toSubgraph.verts=C.toSubgraph.verts := by
  intro i
  apply Set.inter_eq_right.mpr
  intro x hx
  have hsub : C.toSubgraph.verts \ {x} ⊆ G.neighborSet x := by
    intro y hy
    change (G.induce C.toSubgraph.verts).Adj ⟨x,hx⟩ ⟨y,hy.1⟩
    rw [htop]
    intro he
    exact hy.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val he).symm)
  have hb := Set.ncard_mono hsub
  have hv := Set.ncard_diff_singleton_add_one hx
  have hsize : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC]
  rw [hsize,hlen] at hv
  exact (p i).mem_verts_toSubgraph.mpr (high_degree_on_every_path C hC a b p hp hc x (by omega) i)

end Erdos583CycleOneCoreGapDevelopment
