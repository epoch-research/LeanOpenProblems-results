import Submission.Work
/-! API check for finite auxiliary obstruction. -/
open SimpleGraph Erdos583Work
#check Set.eq_univ_of_ncard
#check Set.eq_univ_of_ncard_eq
#check Set.ncard_eq_iff
#check Walk.IsPath.length_lt
#check Walk.IsPath.length_lt_card
#check Walk.IsPath.isHamiltonian_iff
#check QuotaTrails.TrailFamily
#check Subgraph.spanningCoe
#check ncard_neighbor_sup
#check Set.ncard_union_eq
#check degree_sum_of_edge_partition
#check QuotaParity.degree_sum
#check RootCapacity.path_incidence
#check path_neighbor_ncard_le_two
#check path_neighbor_ncard_formula
