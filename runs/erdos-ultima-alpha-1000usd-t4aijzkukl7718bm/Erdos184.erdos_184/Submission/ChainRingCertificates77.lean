import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert539 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))}
  rank := fun | .inl h => ![0,2,0,0,4,0,0] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,none,some (Sum.inr (0,1)),none,none] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert539_valid : cert539.Valid (canonical true ![4,0,0]) := by
  decide +kernel
lemma case539 : ForestBound (canonical true ![4,0,0]) := CycleForestCertificate.Data.forestBound cert539_valid
def cert540 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,2] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert540_valid : cert540.Valid (canonical true ![4,0,1]) := by
  decide +kernel
lemma case540 : ForestBound (canonical true ![4,0,1]) := CycleForestCertificate.Data.forestBound cert540_valid
def cert541 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert541_valid : cert541.Valid (canonical true ![4,0,2]) := by
  decide +kernel
lemma case541 : ForestBound (canonical true ![4,0,2]) := CycleForestCertificate.Data.forestBound cert541_valid
def cert542 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert542_valid : cert542.Valid (canonical true ![4,0,3]) := by
  decide +kernel
lemma case542 : ForestBound (canonical true ![4,0,3]) := CycleForestCertificate.Data.forestBound cert542_valid
def cert543 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert543_valid : cert543.Valid (canonical true ![4,0,4]) := by
  decide +kernel
lemma case543 : ForestBound (canonical true ![4,0,4]) := CycleForestCertificate.Data.forestBound cert543_valid
def cert544 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert544_valid : cert544.Valid (canonical true ![4,0,5]) := by
  decide +kernel
lemma case544 : ForestBound (canonical true ![4,0,5]) := CycleForestCertificate.Data.forestBound cert544_valid
def cert545 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert545_valid : cert545.Valid (canonical true ![4,0,6]) := by
  decide +kernel
lemma case545 : ForestBound (canonical true ![4,0,6]) := CycleForestCertificate.Data.forestBound cert545_valid

end Erdos184Work.ChainRing
