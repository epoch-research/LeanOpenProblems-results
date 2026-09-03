import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert448 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,0] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),none] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert448_valid : cert448.Valid (canonical true ![2,1,0]) := by
  decide +kernel
lemma case448 : ForestBound (canonical true ![2,1,0]) := CycleForestCertificate.Data.forestBound cert448_valid
def cert449 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,6] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![5,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert449_valid : cert449.Valid (canonical true ![2,1,1]) := by
  decide +kernel
lemma case449 : ForestBound (canonical true ![2,1,1]) := CycleForestCertificate.Data.forestBound cert449_valid
def cert450 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,6] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![5,7,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),none,none,none,none]] i j
lemma cert450_valid : cert450.Valid (canonical true ![2,1,2]) := by
  decide +kernel
lemma case450 : ForestBound (canonical true ![2,1,2]) := CycleForestCertificate.Data.forestBound cert450_valid
def cert451 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,6] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![5,7,7,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none,none]] i j
lemma cert451_valid : cert451.Valid (canonical true ![2,1,3]) := by
  decide +kernel
lemma case451 : ForestBound (canonical true ![2,1,3]) := CycleForestCertificate.Data.forestBound cert451_valid
def cert452 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,6] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![5,7,7,7,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert452_valid : cert452.Valid (canonical true ![2,1,4]) := by
  decide +kernel
lemma case452 : ForestBound (canonical true ![2,1,4]) := CycleForestCertificate.Data.forestBound cert452_valid
def cert453 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,4)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,6] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![5,7,7,7,7,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert453_valid : cert453.Valid (canonical true ![2,1,5]) := by
  decide +kernel
lemma case453 : ForestBound (canonical true ![2,1,5]) := CycleForestCertificate.Data.forestBound cert453_valid
def cert454 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 0),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,5)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (2,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,6] h | .inr (i,j) => ![![1,3,0,0,0,0],![3,0,0,0,0,0],![5,7,7,7,7,7]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert454_valid : cert454.Valid (canonical true ![2,1,6]) := by
  decide +kernel
lemma case454 : ForestBound (canonical true ![2,1,6]) := CycleForestCertificate.Data.forestBound cert454_valid

end Erdos184Work.ChainRing
