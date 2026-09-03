import Submission.TightDual

/-! A finite obstruction to contraction control of the integral--fractional gap.
This is auxiliary research, not a disproof of Erdős 184. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGapTest
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

def edges : Finset (Sym2 (Fin 29)) :=
  {s(0,7), s(0,8), s(0,9), s(1,5), s(1,8), s(1,12), s(2,3), s(2,4), s(2,12), s(2,14), s(3,7), s(3,12), s(3,13), s(4,9), s(4,11), s(4,14), s(5,6), s(5,11), s(5,12), s(6,10), s(6,11), s(6,13), s(7,9), s(7,13), s(8,10), s(8,14), s(9,11), s(10,13), s(10,14), s(1,21), s(1,22), s(1,23), s(15,19), s(15,22), s(15,26), s(16,17), s(16,18), s(16,26), s(16,28), s(17,21), s(17,26), s(17,27), s(18,23), s(18,25), s(18,28), s(19,20), s(19,25), s(19,26), s(20,24), s(20,25), s(20,27), s(21,23), s(21,27), s(22,24), s(22,28), s(23,25), s(24,27), s(24,28), s(0,15)}

def graph : SimpleGraph (Fin 29) := SimpleGraph.fromEdgeSet edges
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def contracted : SimpleGraph (Fin 29) := CertificateStructure.contract graph 0 15
instance : DecidableRel contracted.Adj := by unfold contracted CertificateStructure.contract; infer_instance

set_option profiler true
lemma graph_even : ∀ v, Even (graph.degree v) := by
  intro v
  fin_cases v <;> decide
#print axioms graph_even
end Erdos184Work.ContractionGapTest
