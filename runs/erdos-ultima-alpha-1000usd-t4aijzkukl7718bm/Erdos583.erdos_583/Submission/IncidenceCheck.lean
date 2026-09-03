import Submission.Work
/-! API check for incidence counts. -/
open SimpleGraph Erdos583Work
#check List.count_cons
#check List.countP_cons
#check List.count_eq_one_of_mem
#check List.count_eq_zero_of_not_mem
#check List.length_filter
#check List.countP_eq_length_filter
#check List.toFinset_filter
#check List.Nodup.filter
#check List.toFinset_card_of_nodup
#check Walk.IsTrail.edgesFinset
#check Walk.IsEulerian.edgesFinset_eq
#check Subgraph.neighborSet_sup
#check SimpleGraph.card_neighborSet_eq_degree
#check Finset.sum_ite_irrel
#check Walk.toSubgraph_cons
#check Walk.IsPath.support_nodup
#check Sym2.mem_iff
