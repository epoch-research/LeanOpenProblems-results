import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert685 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 1),(Sum.inr (0,3))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 1),(Sum.inr (0,5))),s((Sum.inl 1),(Sum.inr (1,4))),s((Sum.inl 2),(Sum.inr (1,5))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 4),(Sum.inr (0,4))),s((Sum.inl 4),(Sum.inr (0,5))),s((Sum.inl 5),(Sum.inr (1,4))),s((Sum.inl 5),(Sum.inr (1,5))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,3)))},{s((Sum.inl 0),(Sum.inr (0,5)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,4)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,3)))},{s((Sum.inl 1),(Sum.inr (1,5)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,4)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,4))),s((Sum.inl 4),(Sum.inr (0,5))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,4))),s((Sum.inl 5),(Sum.inr (1,5))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,2,4,0,4,6,6] h | .inr (i,j) => ![![1,3,5,5,5,5],![3,5,7,7,7,7],![5,7,7,7,7,7]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),some (Sum.inl 4),some (Sum.inl 4)],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),some (Sum.inl 5),some (Sum.inl 5)],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert685_valid : cert685.Valid (canonical true ![6,6,6]) := by
  decide +kernel
lemma case685 : ForestBound (canonical true ![6,6,6]) := CycleForestCertificate.Data.forestBound cert685_valid

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.case685
