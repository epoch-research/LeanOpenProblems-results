import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert392 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,0,0,2,0,0] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,none,some (Sum.inr (0,0)),none,none] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert392_valid : cert392.Valid (canonical true ![1,0,0]) := by
  decide +kernel
lemma case392 : ForestBound (canonical true ![1,0,0]) := CycleForestCertificate.Data.forestBound cert392_valid
def cert393 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,2,2,0,2,0,2] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert393_valid : cert393.Valid (canonical true ![1,0,1]) := by
  decide +kernel
lemma case393 : ForestBound (canonical true ![1,0,1]) := CycleForestCertificate.Data.forestBound cert393_valid
def cert394 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,2,2,0,2,0,4] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,0)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert394_valid : cert394.Valid (canonical true ![1,0,2]) := by
  decide +kernel
lemma case394 : ForestBound (canonical true ![1,0,2]) := CycleForestCertificate.Data.forestBound cert394_valid
def cert395 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,2,2,0,2,0,4] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,0)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert395_valid : cert395.Valid (canonical true ![1,0,3]) := by
  decide +kernel
lemma case395 : ForestBound (canonical true ![1,0,3]) := CycleForestCertificate.Data.forestBound cert395_valid
def cert396 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,2,2,0,2,0,4] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,0)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert396_valid : cert396.Valid (canonical true ![1,0,4]) := by
  decide +kernel
lemma case396 : ForestBound (canonical true ![1,0,4]) := CycleForestCertificate.Data.forestBound cert396_valid
def cert397 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,2,2,0,2,0,4] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,0)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert397_valid : cert397.Valid (canonical true ![1,0,5]) := by
  decide +kernel
lemma case397 : ForestBound (canonical true ![1,0,5]) := CycleForestCertificate.Data.forestBound cert397_valid
def cert398 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,2,2,0,2,0,4] h | .inr (i,j) => ![![1,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (2,0)),none,some (Sum.inr (0,0)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert398_valid : cert398.Valid (canonical true ![1,0,6]) := by
  decide +kernel
lemma case398 : ForestBound (canonical true ![1,0,6]) := CycleForestCertificate.Data.forestBound cert398_valid

end Erdos184Work.ChainRing
