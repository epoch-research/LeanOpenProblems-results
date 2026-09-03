import Submission.DoublePetersenCore
import Submission.LabelKernelRealization
import Submission.PathKernelDifference

/-! A simple even graph that is cycle-critical but not even-minimal.
This auxiliary counterexample does not disprove Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DoublePetersenGraph
open Critical EvenCore Rigidity Erdos184Serial DoublePetersen
set_option maxHeartbeats 3000000
abbrev Vertex := DoublePetersen.Vertex ⊕ DoublePetersen.Edge

def graph : SimpleGraph Vertex := LabelKernel.Realization.graph src dst
lemma loopless : ∀ e, src e ≠ dst e := fun e => PetersenBase.src_ne_dst e.1

def family : PathSubstitution.Family DoublePetersen.Edge DoublePetersen.Vertex graph :=
  LabelKernel.Realization.family src dst loopless

lemma cover (x y : Vertex) (h : graph.Adj x y) : ∃ e, s(x,y) ∈ (family.path e).edges :=
  LabelKernel.Realization.cover src dst loopless x y h

lemma valid_eq (s : Finset DoublePetersen.Edge) : family.validLabels s ↔ DoublePetersen.code.valid s := by
  unfold PathSubstitution.Family.validLabels DoublePetersen.code LabelKernel.code LabelKernel.valid
  dsimp [family, LabelKernel.Realization.family]
  apply forall_congr'
  intro w
  apply iff_of_eq
  congr 2
  ext j
  simp

lemma number_iff (s : Finset DoublePetersen.Edge) (k : ℕ) :
    @HasNumber _ (Classical.decEq _) (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) family.src family.dst) s k ↔
      HasNumber DoublePetersen.code s k := by
  have hE : Classical.decEq DoublePetersen.Edge = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  have hW : Classical.decEq DoublePetersen.Vertex = instDecidableEqFin 10 := Subsingleton.elim _ _
  rw [hE,hW]
  rfl

lemma minimal_iff (s : Finset DoublePetersen.Edge) (k : ℕ) :
    @MinimalCore _ (Classical.decEq _) (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) family.src family.dst) s k ↔
      MinimalCore DoublePetersen.code s k := by
  have hE : Classical.decEq DoublePetersen.Edge = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  have hW : Classical.decEq DoublePetersen.Vertex = instDecidableEqFin 10 := Subsingleton.elim _ _
  rw [hE,hW]
  rfl

lemma circuit_iff (s : Finset DoublePetersen.Edge) :
    @Circuit _ (Classical.decEq _) (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) family.src family.dst) s ↔
      Circuit DoublePetersen.code s := by
  have hE : Classical.decEq DoublePetersen.Edge = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  have hW : Classical.decEq DoublePetersen.Vertex = instDecidableEqFin 10 := Subsingleton.elim _ _
  rw [hE,hW]
  rfl

lemma even : ∀ x, Even (graph.degree x) := by
  have hh := (family.expandGraph_even_iff Finset.univ).mpr ((valid_eq _).mpr DoublePetersen.full_valid)
  rw [family.expandGraph_univ cover] at hh
  exact hh

lemma number_eq_five : number graph = 5 :=
  (family.number_iff_kernel_full cover even 5).mpr ((number_iff _ _).mpr DoublePetersen.full_number)

lemma not_minimal : ¬ EvenMinimal graph := by
  intro h
  apply DoublePetersen.not_minimal
  apply (minimal_iff _ _).mp
  apply (family.minimal_expandGraph_iff cover Finset.univ ((valid_eq _).mpr DoublePetersen.full_valid) 5).mp
  rw [family.expandGraph_univ cover]
  exact ⟨h,number_eq_five⟩

lemma cycle_critical : CycleCritical graph := by
  letI : DecidableEq Vertex := Classical.decEq _
  intro u p hp
  have hcyc : p.toSubgraph.coe.Connected ∧ p.toSubgraph.coe.IsRegularOfDegree 2 :=
    cycle_coe_regular graph hp
  have hC : Circuit (GraphCircuitCode.code graph) p.toSubgraph.spanningCoe.edgeFinset :=
    (GraphCircuitCode.circuit_iff_number_one p.toSubgraph.spanningCoe_le
      (cycle_spanning_even graph hp)).mpr (GraphCircuitCode.cycle_number_one p.toSubgraph hcyc)
  have hfull : family.expandEdges Finset.univ = graph.edgeFinset := by
    rw [← family.expandGraph_edgeFinset,family.expandGraph_univ cover]
  have hsub : p.toSubgraph.spanningCoe.edgeFinset ⊆ family.expandEdges Finset.univ := by
    rw [hfull]
    exact SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le
  obtain ⟨t,ht⟩ := (@SupportTransport.lift _ _ (Classical.decEq _) (inferInstance) _ _
    (family.supportTransport cover)) Finset.univ
    p.toSubgraph.spanningCoe.edgeFinset hsub hC.1
  change family.expandEdges t = p.toSubgraph.spanningCoe.edgeFinset at ht
  have hc : Circuit DoublePetersen.code t := by
    apply (circuit_iff t).mp
    apply (@SupportTransport.circuit_iff _ _ (Classical.decEq _) (inferInstance) _ _
      (family.supportTransport cover) t).mp
    change Circuit (GraphCircuitCode.code graph) (family.expandEdges t)
    rw [ht]
    exact hC
  have htg : family.expandGraph t = p.toSubgraph.spanningCoe := by
    apply SimpleGraph.edgeFinset_inj.mp
    rw [family.expandGraph_edgeFinset,ht]
  have hv : DoublePetersen.code.valid (Finset.univ \ t) :=
    DoublePetersen.code.diff DoublePetersen.full_valid hc.1 (Finset.subset_univ t)
  have hn := (family.number_expandGraph_iff cover (Finset.univ \ t) ((valid_eq _).mpr hv) 4).mpr
    ((number_iff _ _).mpr (DoublePetersen.cofactor_number t hc))
  have hE : Classical.decEq DoublePetersen.Edge = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  rw [← hE] at hn
  rw [family.expandGraph_sdiff,family.expandGraph_univ cover,htg] at hn
  rw [number_eq_five,hn]

lemma counterexample : (∀ x, Even (graph.degree x)) ∧ CycleCritical graph ∧
    number graph = 5 ∧ ¬ EvenMinimal graph :=
  ⟨even,cycle_critical,number_eq_five,not_minimal⟩

#print axioms counterexample
#print axioms cycle_critical
end Erdos184Work.DoublePetersenGraph
