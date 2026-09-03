import Submission.PathKernelTransport

/-! Path-kernel expansion commutes with edge-set difference. -/
open SimpleGraph
namespace Erdos184Work.PathSubstitution.Family
variable {V W E : Type*} [Fintype V] [Fintype E] {G : SimpleGraph V}
variable (F : Family E W G)
open scoped Classical

lemma expandEdges_sdiff (s t : Finset E) :
    F.expandEdges (s \ t) = F.expandEdges s \ F.expandEdges t := by
  ext e
  simp only [expandEdges,Finset.mem_biUnion,Finset.mem_sdiff,List.mem_toFinset]
  constructor
  · rintro ⟨i,⟨his,hit⟩,hei⟩
    refine ⟨⟨i,his,hei⟩,?_⟩
    rintro ⟨j,hjt,hej⟩
    by_cases hij : i = j
    · exact hit (hij.symm ▸ hjt)
    · exact List.disjoint_left.mp (F.edge_disjoint i j hij) hei hej
  · rintro ⟨⟨i,his,hei⟩,hn⟩
    exact ⟨i,⟨his,fun hit => hn ⟨i,hit,hei⟩⟩,hei⟩

lemma expandGraph_sdiff (s t : Finset E) :
    F.expandGraph (s \ t) = F.expandGraph s \ F.expandGraph t := by
  apply SimpleGraph.edgeFinset_inj.mp
  rw [SimpleGraph.edgeFinset_sdiff,F.expandGraph_edgeFinset,F.expandGraph_edgeFinset,
    F.expandGraph_edgeFinset,F.expandEdges_sdiff]

#print axioms expandGraph_sdiff
end Erdos184Work.PathSubstitution.Family
