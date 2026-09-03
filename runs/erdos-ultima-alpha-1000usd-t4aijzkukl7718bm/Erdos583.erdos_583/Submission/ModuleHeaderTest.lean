import FormalConjecturesUtil

/-!
Partial results for Erdős Problem 583. This file does not prove the general conjecture.
Verified cases include forests, connected graphs with at most as many edges as vertices,
all maximum-degree-three graphs and their iterated pendant-cycle extensions,
complete graphs with an arbitrary matching removed, and even-order complete graphs
with a subset of a spanning cycle removed. The all-odd-degree case is proved by
a global normal-trail exchange argument, including prescribed first-edge flexibility
and deletion of one edge from an all-odd graph. The bound is also proved for every
graph with at most three even-degree vertices. Pendant projection gives normal
path decompositions for all finite graphs and an exact inactive-vertex counting
reduction, without assuming the missing endpoint-selection bound. Rooted exchanges
include degree-controlled simultaneous preservation of outside members. Eulerian
normal partitions have a permutation-path representation, with inactive vertices
exactly the fixed points; the required fixed-point bound remains unproved. The file
also contains path-restoration criteria and conditional reductions. Simultaneous
forbidden-partner avoidance is proved for all-odd forests, giving the bound
after adding an arbitrary matching to an all-odd forest. The same bound holds
after adding a matching between distinct components of any all-odd graph.
-/

set_option Elab.async false

