import Submission.LowDegreeHull
open SimpleGraph
#synth Decidable ((⊥ : SimpleGraph (Fin 25)).Connected)
#synth Decidable ((⊥ : SimpleGraph (Fin 25)).IsAcyclic)
#check SimpleGraph.connectedComponentEquivQuotient
#check SimpleGraph.IsAcyclic.sup
#check SimpleGraph.Iso.map
#check SimpleGraph.Subgraph.top
#check Finset.equivOfCardEq
#check Equiv.Set.compl
#check Equiv.Set.sumCompl
#check SimpleGraph.connected_iff
#check SimpleGraph.Subgraph.spanningCoe_toSubgraph
#check SimpleGraph.connected_iff_exists_forall_reachable
