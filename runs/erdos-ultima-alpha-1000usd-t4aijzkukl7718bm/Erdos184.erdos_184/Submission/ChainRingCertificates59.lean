import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert413 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,0] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![none,none,none,none,none,none]] i j
lemma cert413_valid : cert413.Valid (canonical true ![1,3,0]) := by
  decide +kernel
lemma case413 : ForestBound (canonical true ![1,3,0]) := CycleForestCertificate.Data.forestBound cert413_valid
def cert414 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert414_valid : cert414.Valid (canonical true ![1,3,1]) := by
  decide +kernel
lemma case414 : ForestBound (canonical true ![1,3,1]) := CycleForestCertificate.Data.forestBound cert414_valid
def cert415 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 6),none,none,none,none]] i j
lemma cert415_valid : cert415.Valid (canonical true ![1,3,2]) := by
  decide +kernel
lemma case415 : ForestBound (canonical true ![1,3,2]) := CycleForestCertificate.Data.forestBound cert415_valid
def cert416 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,7,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none,none]] i j
lemma cert416_valid : cert416.Valid (canonical true ![1,3,3]) := by
  decide +kernel
lemma case416 : ForestBound (canonical true ![1,3,3]) := CycleForestCertificate.Data.forestBound cert416_valid
def cert417 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (2,2)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,7,7,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert417_valid : cert417.Valid (canonical true ![1,3,4]) := by
  decide +kernel
lemma case417 : ForestBound (canonical true ![1,3,4]) := CycleForestCertificate.Data.forestBound cert417_valid
def cert418 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,4)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,7,7,7,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert418_valid : cert418.Valid (canonical true ![1,3,5]) := by
  decide +kernel
lemma case418 : ForestBound (canonical true ![1,3,5]) := CycleForestCertificate.Data.forestBound cert418_valid
def cert419 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,5)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (2,2)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,7,7,7,7]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert419_valid : cert419.Valid (canonical true ![1,3,6]) := by
  decide +kernel
lemma case419 : ForestBound (canonical true ![1,3,6]) := CycleForestCertificate.Data.forestBound cert419_valid

end Erdos184Work.ChainRing
