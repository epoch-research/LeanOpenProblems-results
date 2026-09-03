import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert343 : CycleForestCertificate.Data Vertex where
  pieces := ∅
  forest := ∅
  rank := fun | .inl h => ![0,0,0,0,0,0,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,none,none,none,none,none] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert343_valid : cert343.Valid (canonical true ![0,0,0]) := by
  decide +kernel
lemma case343 : ForestBound (canonical true ![0,0,0]) := CycleForestCertificate.Data.forestBound cert343_valid
def cert344 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,0,2,0,0,0,2] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (2,0)),none,none,none,some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert344_valid : cert344.Valid (canonical true ![0,0,1]) := by
  decide +kernel
lemma case344 : ForestBound (canonical true ![0,0,1]) := CycleForestCertificate.Data.forestBound cert344_valid
def cert345 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,0,2,0,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (2,0)),none,none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert345_valid : cert345.Valid (canonical true ![0,0,2]) := by
  decide +kernel
lemma case345 : ForestBound (canonical true ![0,0,2]) := CycleForestCertificate.Data.forestBound cert345_valid
def cert346 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,0,2,0,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (2,0)),none,none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert346_valid : cert346.Valid (canonical true ![0,0,3]) := by
  decide +kernel
lemma case346 : ForestBound (canonical true ![0,0,3]) := CycleForestCertificate.Data.forestBound cert346_valid
def cert347 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,0,2,0,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (2,0)),none,none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert347_valid : cert347.Valid (canonical true ![0,0,4]) := by
  decide +kernel
lemma case347 : ForestBound (canonical true ![0,0,4]) := CycleForestCertificate.Data.forestBound cert347_valid
def cert348 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,0,2,0,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (2,0)),none,none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert348_valid : cert348.Valid (canonical true ![0,0,5]) := by
  decide +kernel
lemma case348 : ForestBound (canonical true ![0,0,5]) := CycleForestCertificate.Data.forestBound cert348_valid
def cert349 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,0,2,0,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (2,0)),none,none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert349_valid : cert349.Valid (canonical true ![0,0,6]) := by
  decide +kernel
lemma case349 : ForestBound (canonical true ![0,0,6]) := CycleForestCertificate.Data.forestBound cert349_valid

end Erdos184Work.ChainRing
