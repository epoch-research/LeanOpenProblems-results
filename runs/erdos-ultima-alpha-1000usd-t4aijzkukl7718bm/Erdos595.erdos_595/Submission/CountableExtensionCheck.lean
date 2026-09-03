import Submission.CountableExtensionGraph
open Erdos595CountableExtension SimpleGraph Set
set_option pp.all true in
#check pair_triangleFree
example (v : Vertex) : (G.induce (↑({v} : Finset Vertex) : Set Vertex)).CliqueFree 3 := by
  classical
  apply SimpleGraph.cliqueFree_of_card_lt
  rw [Fintype.card_coe, Finset.card_singleton]
  decide
