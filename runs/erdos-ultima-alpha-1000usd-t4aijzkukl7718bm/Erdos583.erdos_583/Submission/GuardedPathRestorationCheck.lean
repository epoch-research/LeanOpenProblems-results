import Submission.GuardedPathRestoration
/-! API checks for guarded restoration. -/
open SimpleGraph Erdos583Work
#check ncard_neighbor_delete_subgraph_add
#check Walk.IsPath.neighborSet_toSubgraph_startpoint
#check Walk.IsPath.neighborSet_toSubgraph_endpoint
#check Walk.IsPath.neighborSet_toSubgraph_endpoint_eq
#check TipParity.delete_path_degree_parity
#check SimpleGraph.Reachable.exists_path_of_dist
#check SimpleGraph.SimpleGraph.dist_eq_one_iff_adj
#check SimpleGraph.dist_eq_one_iff_adj
#check SimpleGraph.Walk.IsPath.of_append_left
