import Submission.DoublePetersenGraph
import Submission.PetersenSquareLower
import Submission.PathKernelCritical

/-! No square of the doubled-Petersen simple subdivision has a cycle-critical
cofactor. The graph itself is cycle-critical. This is not a disproof of Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DoublePetersenGraph
open Critical EvenCore Rigidity Erdos184Serial DoublePetersen LabelKernel
set_option maxHeartbeats 3000000

lemma pair_cofactor_not_critical (e : Fin 15) :
    ¬ CycleCritical (graph \ family.expandGraph (Parallel.pair e)) := by
  have hE : Classical.decEq DoublePetersen.Edge = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  let s := Finset.univ \ Parallel.pair e
  let t := Parallel.pair (SquareLower.nextEdge e)
  have hs : DoublePetersen.code.valid s :=
    DoublePetersen.code.diff full_valid (SquareLower.pair_circuit e).1 (Finset.subset_univ _)
  have ht : Circuit DoublePetersen.code t := SquareLower.pair_circuit _
  have hts : t ⊆ s := Finset.subset_sdiff.mpr ⟨Finset.subset_univ _,(SquareLower.pairs_disjoint e).symm⟩
  have hn := (family.number_expandGraph_iff cover s ((valid_eq _).mpr hs) 4).mpr
    ((number_iff _ _).mpr (cofactor_number (Parallel.pair e) (SquareLower.pair_circuit e)))
  have hr := (family.number_expandGraph_iff cover (SquareLower.rest e)
    ((valid_eq _).mpr (SquareLower.rest_valid e)) (number (family.expandGraph (SquareLower.rest e)))).mp rfl
  have hr' := (number_iff _ _).mp hr
  obtain ⟨D,hD,hcard⟩ := hr'.1
  have hl := SquareLower.lower e D hD
  intro hc
  have hcs : CycleCritical (family.expandGraph s) := by
    dsimp [s]
    rw [← hE,family.expandGraph_sdiff,family.expandGraph_univ cover]
    exact hc
  have hh := family.critical_cofactor cover s t hcs ((circuit_iff _).mpr ht) hts
  have heq : @sdiff (Finset DoublePetersen.Edge)
      (@Finset.instSDiff _ (fun a b => Classical.propDecidable (a = b))) s t = SquareLower.rest e := by
    ext x
    simp [s,t,SquareLower.rest]
  rw [heq,hn] at hh
  omega

lemma expand_card (s : Finset DoublePetersen.Edge) : (family.expandEdges s).card = 2 * s.card := by
  letI : DecidableEq Vertex := Classical.decEq _
  have hd : Set.PairwiseDisjoint (s : Set DoublePetersen.Edge)
      (fun e => (family.path e).edges.toFinset) := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact List.disjoint_left.mp (family.edge_disjoint e f hef)
      (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
  have hp (e : DoublePetersen.Edge) : (family.path e).edges.toFinset.card = 2 := by
    have hn := loopless e
    simp [family,LabelKernel.Realization.family,LabelKernel.Realization.path,
      Walk.edges_cons,Walk.edges_nil,hn]
  rw [PathSubstitution.Family.expandEdges,Finset.card_biUnion hd]
  simp only [hp,Finset.sum_const,smul_eq_mul]
  omega

lemma cycle_labels {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) :
    ∃ t : Finset DoublePetersen.Edge, Circuit DoublePetersen.code t ∧
      family.expandGraph t = p.toSubgraph.spanningCoe := by
  letI : DecidableEq Vertex := Classical.decEq _
  have hC : Circuit (GraphCircuitCode.code graph) p.toSubgraph.spanningCoe.edgeFinset :=
    GraphCircuitCode.cycle_circuit p.toSubgraph (cycle_coe_regular graph hp)
  have hfull : family.expandEdges Finset.univ = graph.edgeFinset := by
    rw [← family.expandGraph_edgeFinset,family.expandGraph_univ cover]
  have hsub : p.toSubgraph.spanningCoe.edgeFinset ⊆ family.expandEdges Finset.univ := by
    rw [hfull]
    exact SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le
  obtain ⟨t,ht⟩ := (@SupportTransport.lift _ _ (Classical.decEq _) (inferInstance) _ _
    (family.supportTransport cover)) Finset.univ
    p.toSubgraph.spanningCoe.edgeFinset hsub hC.1
  change family.expandEdges t = p.toSubgraph.spanningCoe.edgeFinset at ht
  refine ⟨t,?_,?_⟩
  · apply (circuit_iff t).mp
    apply (@SupportTransport.circuit_iff _ _ (Classical.decEq _) (inferInstance) _ _
      (family.supportTransport cover) t).mp
    change Circuit (GraphCircuitCode.code graph) (family.expandEdges t)
    rw [ht]
    exact hC
  · apply SimpleGraph.edgeFinset_inj.mp
    rw [family.expandGraph_edgeFinset,ht]

lemma base_cycle_large : ∀ i : Fin 57, 5 ≤ (PetersenBase.edges i).card := by decide +kernel

lemma square_labels {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) (hl : p.length = 4) :
    ∃ e : Fin 15, family.expandGraph (Parallel.pair e) = p.toSubgraph.spanningCoe := by
  obtain ⟨t,ht,hg⟩ := cycle_labels p hp
  have hcard : t.card = 2 := by
    letI : DecidableEq Vertex := Classical.decEq _
    have he := congrArg (fun R : SimpleGraph Vertex => R.edgeFinset.card) hg
    dsimp only at he
    rw [family.expandGraph_edgeFinset,expand_card,cycle_edge_count graph hp,hl] at he
    omega
  rcases Parallel.circuit_cases PetersenBase.src PetersenBase.dst ht with ⟨e,rfl⟩ | ⟨a,b,ha,he⟩
  · exact ⟨e,hg⟩
  · obtain ⟨i,rfl⟩ := PetersenBase.catalogue a ha
    rw [he,Finset.card_map] at hcard
    have hb := base_cycle_large i
    omega

lemma no_square_critical_cofactor {u : Vertex} (p : graph.Walk u u)
    (hp : p.IsCycle) (hl : p.length = 4) :
    ¬ CycleCritical (graph \ p.toSubgraph.spanningCoe) := by
  obtain ⟨e,he⟩ := square_labels p hp hl
  rw [← he]
  exact pair_cofactor_not_critical e

def squareWalk (e : Fin 15) : graph.Walk (.inl (PetersenBase.src e)) (.inl (PetersenBase.src e)) :=
  .cons (show graph.Adj (.inl (PetersenBase.src e)) (.inr (e,false)) from Or.inl rfl)
    (.cons (show graph.Adj (.inr (e,false)) (.inl (PetersenBase.dst e)) from Or.inr rfl)
      (.cons (show graph.Adj (.inl (PetersenBase.dst e)) (.inr (e,true)) from Or.inr rfl)
        (.cons (show graph.Adj (.inr (e,true)) (.inl (PetersenBase.src e)) from Or.inl rfl) .nil)))

lemma squareWalk_cycle : ∀ e, (squareWalk e).IsCycle := by
  intro e
  rw [Walk.isCycle_def,Walk.isTrail_def]
  have hn := PetersenBase.src_ne_dst e
  simp [squareWalk,Walk.edges_cons,Walk.support_cons,Sym2.eq_iff,hn,Ne.symm hn]
lemma squareWalk_length (e : Fin 15) : (squareWalk e).length = 4 := rfl

lemma square_critical_obstruction :
    (∀ v, Even (graph.degree v)) ∧ CycleCritical graph ∧ number graph = 5 ∧
    (∃ u, ∃ p : graph.Walk u u, p.IsCycle ∧ p.length = 4) ∧
    (∀ u (p : graph.Walk u u), p.IsCycle → p.length = 4 →
      ¬ CycleCritical (graph \ p.toSubgraph.spanningCoe)) := by
  exact ⟨even,cycle_critical,number_eq_five,
    ⟨_,squareWalk 0,squareWalk_cycle 0,squareWalk_length 0⟩,
    fun _ p hp hl => no_square_critical_cofactor p hp hl⟩

#print axioms square_critical_obstruction
#print axioms pair_cofactor_not_critical
#print axioms no_square_critical_cofactor
end Erdos184Work.DoublePetersenGraph
