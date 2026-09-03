import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert490 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2)))}
  rank := fun | .inl h => ![0,2,0,0,4,0,0] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,none,some (Sum.inr (0,1)),none,none] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert490_valid : cert490.Valid (canonical true ![3,0,0]) := by
  decide +kernel
lemma case490 : ForestBound (canonical true ![3,0,0]) := CycleForestCertificate.Data.forestBound cert490_valid
def cert491 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,2] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert491_valid : cert491.Valid (canonical true ![3,0,1]) := by
  decide +kernel
lemma case491 : ForestBound (canonical true ![3,0,1]) := CycleForestCertificate.Data.forestBound cert491_valid
def cert492 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert492_valid : cert492.Valid (canonical true ![3,0,2]) := by
  decide +kernel
lemma case492 : ForestBound (canonical true ![3,0,2]) := CycleForestCertificate.Data.forestBound cert492_valid
def cert493 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert493_valid : cert493.Valid (canonical true ![3,0,3]) := by
  decide +kernel
lemma case493 : ForestBound (canonical true ![3,0,3]) := CycleForestCertificate.Data.forestBound cert493_valid
def cert494 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert494_valid : cert494.Valid (canonical true ![3,0,4]) := by
  decide +kernel
lemma case494 : ForestBound (canonical true ![3,0,4]) := CycleForestCertificate.Data.forestBound cert494_valid
def cert495 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert495_valid : cert495.Valid (canonical true ![3,0,5]) := by
  decide +kernel
lemma case495 : ForestBound (canonical true ![3,0,5]) := CycleForestCertificate.Data.forestBound cert495_valid
def cert496 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,2,2,0,4,0,4] h | .inr (i,j) => ![![1,3,5,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert496_valid : cert496.Valid (canonical true ![3,0,6]) := by
  decide +kernel
lemma case496 : ForestBound (canonical true ![3,0,6]) := CycleForestCertificate.Data.forestBound cert496_valid

end Erdos184Work.ChainRing
