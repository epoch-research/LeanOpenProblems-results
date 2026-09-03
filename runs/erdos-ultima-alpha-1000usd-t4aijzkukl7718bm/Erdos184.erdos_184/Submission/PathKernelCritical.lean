import Submission.PathKernelDifference

/-! Cycle criticality transported to finite labelled path kernels. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSubstitution.Family
open Erdos184Serial Critical EvenCore
variable {V W J : Type*} [Fintype V] [Fintype J] {G : SimpleGraph V}
variable (F : Family J W G)
set_option maxHeartbeats 2000000

lemma critical_cofactor
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s t : Finset J) (hc : CycleCritical (F.expandGraph s))
    (ht : Circuit (LabelKernel.code F.src F.dst) t) (hts : t ⊆ s) :
    number (F.expandGraph s) = number (F.expandGraph (s \ t)) + 1 := by
  have hct : Circuit (GraphCircuitCode.code G) (F.expandGraph t).edgeFinset := by
    rw [F.expandGraph_edgeFinset]
    exact (F.supportTransport hcover).circuit_iff t |>.mpr ht
  have he : ∀ x, Even ((F.expandGraph t).degree x) := (F.expandGraph_even_iff t).mpr ht.1
  have hn : number (F.expandGraph t) = 1 :=
    (GraphCircuitCode.circuit_iff_number_one (F.expandGraph_le t) he).mp hct
  have hct' : Circuit (GraphCircuitCode.code (F.expandGraph s)) (F.expandGraph t).edgeFinset :=
    (GraphCircuitCode.circuit_iff_number_one (F.expandGraph_mono hts) he).mpr hn
  obtain ⟨H,hH,hE⟩ := GraphCircuitCode.circuit_piece hct'
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) v.val v.property
  have hgraph : p.toSubgraph.spanningCoe = F.expandGraph t := by
    rw [hpH]
    exact SimpleGraph.edgeFinset_inj.mp hE
  have hh := hc v.val p hp
  rw [hgraph,← F.expandGraph_sdiff] at hh
  exact hh

#print axioms critical_cofactor
end Erdos184Work.PathSubstitution.Family
