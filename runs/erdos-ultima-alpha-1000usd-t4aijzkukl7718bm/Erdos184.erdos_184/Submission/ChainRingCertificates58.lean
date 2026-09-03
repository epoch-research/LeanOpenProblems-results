import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert406 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,0] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert406_valid : cert406.Valid (canonical true ![1,2,0]) := by
  decide +kernel
lemma case406 : ForestBound (canonical true ![1,2,0]) := CycleForestCertificate.Data.forestBound cert406_valid
def cert407 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert407_valid : cert407.Valid (canonical true ![1,2,1]) := by
  decide +kernel
lemma case407 : ForestBound (canonical true ![1,2,1]) := CycleForestCertificate.Data.forestBound cert407_valid
def cert408 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),none,none,none,none]] i j
lemma cert408_valid : cert408.Valid (canonical true ![1,2,2]) := by
  decide +kernel
lemma case408 : ForestBound (canonical true ![1,2,2]) := CycleForestCertificate.Data.forestBound cert408_valid
def cert409 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,7,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none,none]] i j
lemma cert409_valid : cert409.Valid (canonical true ![1,2,3]) := by
  decide +kernel
lemma case409 : ForestBound (canonical true ![1,2,3]) := CycleForestCertificate.Data.forestBound cert409_valid
def cert410 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,2)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,7,7,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert410_valid : cert410.Valid (canonical true ![1,2,4]) := by
  decide +kernel
lemma case410 : ForestBound (canonical true ![1,2,4]) := CycleForestCertificate.Data.forestBound cert410_valid
def cert411 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,4)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,7,7,7,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert411_valid : cert411.Valid (canonical true ![1,2,5]) := by
  decide +kernel
lemma case411 : ForestBound (canonical true ![1,2,5]) := CycleForestCertificate.Data.forestBound cert411_valid
def cert412 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,5)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,2)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,7,7,7,7]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert412_valid : cert412.Valid (canonical true ![1,2,6]) := by
  decide +kernel
lemma case412 : ForestBound (canonical true ![1,2,6]) := CycleForestCertificate.Data.forestBound cert412_valid

end Erdos184Work.ChainRing
