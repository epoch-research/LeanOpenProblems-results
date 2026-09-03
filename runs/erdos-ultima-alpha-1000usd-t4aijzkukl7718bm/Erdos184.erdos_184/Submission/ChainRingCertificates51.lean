import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert357 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1)))}
  rank := fun | .inl h => ![0,0,2,0,0,4,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),none,none,some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert357_valid : cert357.Valid (canonical true ![0,2,0]) := by
  decide +kernel
lemma case357 : ForestBound (canonical true ![0,2,0]) := CycleForestCertificate.Data.forestBound cert357_valid
def cert358 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,2] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert358_valid : cert358.Valid (canonical true ![0,2,1]) := by
  decide +kernel
lemma case358 : ForestBound (canonical true ![0,2,1]) := CycleForestCertificate.Data.forestBound cert358_valid
def cert359 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert359_valid : cert359.Valid (canonical true ![0,2,2]) := by
  decide +kernel
lemma case359 : ForestBound (canonical true ![0,2,2]) := CycleForestCertificate.Data.forestBound cert359_valid
def cert360 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert360_valid : cert360.Valid (canonical true ![0,2,3]) := by
  decide +kernel
lemma case360 : ForestBound (canonical true ![0,2,3]) := CycleForestCertificate.Data.forestBound cert360_valid
def cert361 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert361_valid : cert361.Valid (canonical true ![0,2,4]) := by
  decide +kernel
lemma case361 : ForestBound (canonical true ![0,2,4]) := CycleForestCertificate.Data.forestBound cert361_valid
def cert362 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert362_valid : cert362.Valid (canonical true ![0,2,5]) := by
  decide +kernel
lemma case362 : ForestBound (canonical true ![0,2,5]) := CycleForestCertificate.Data.forestBound cert362_valid
def cert363 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert363_valid : cert363.Valid (canonical true ![0,2,6]) := by
  decide +kernel
lemma case363 : ForestBound (canonical true ![0,2,6]) := CycleForestCertificate.Data.forestBound cert363_valid

end Erdos184Work.ChainRing
