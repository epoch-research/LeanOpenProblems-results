import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert350 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,0,0,2,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),none,none,some (Sum.inr (1,0)),none] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert350_valid : cert350.Valid (canonical true ![0,1,0]) := by
  decide +kernel
lemma case350 : ForestBound (canonical true ![0,1,0]) := CycleForestCertificate.Data.forestBound cert350_valid
def cert351 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,4,2,0,0,4,2] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert351_valid : cert351.Valid (canonical true ![0,1,1]) := by
  decide +kernel
lemma case351 : ForestBound (canonical true ![0,1,1]) := CycleForestCertificate.Data.forestBound cert351_valid
def cert352 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,4,2,0,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert352_valid : cert352.Valid (canonical true ![0,1,2]) := by
  decide +kernel
lemma case352 : ForestBound (canonical true ![0,1,2]) := CycleForestCertificate.Data.forestBound cert352_valid
def cert353 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,4,2,0,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert353_valid : cert353.Valid (canonical true ![0,1,3]) := by
  decide +kernel
lemma case353 : ForestBound (canonical true ![0,1,3]) := CycleForestCertificate.Data.forestBound cert353_valid
def cert354 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,4,2,0,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert354_valid : cert354.Valid (canonical true ![0,1,4]) := by
  decide +kernel
lemma case354 : ForestBound (canonical true ![0,1,4]) := CycleForestCertificate.Data.forestBound cert354_valid
def cert355 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,4,2,0,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert355_valid : cert355.Valid (canonical true ![0,1,5]) := by
  decide +kernel
lemma case355 : ForestBound (canonical true ![0,1,5]) := CycleForestCertificate.Data.forestBound cert355_valid
def cert356 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,4,2,0,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert356_valid : cert356.Valid (canonical true ![0,1,6]) := by
  decide +kernel
lemma case356 : ForestBound (canonical true ![0,1,6]) := CycleForestCertificate.Data.forestBound cert356_valid

end Erdos184Work.ChainRing
