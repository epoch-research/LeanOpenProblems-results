import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert70 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,0] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![none,none,none,none,none,none]] i j
lemma cert70_valid : cert70.Valid (canonical false ![1,3,0]) := by
  decide +kernel
lemma case70 : ForestBound (canonical false ![1,3,0]) := CycleForestCertificate.Data.forestBound cert70_valid
def cert71 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert71_valid : cert71.Valid (canonical false ![1,3,1]) := by
  decide +kernel
lemma case71 : ForestBound (canonical false ![1,3,1]) := CycleForestCertificate.Data.forestBound cert71_valid
def cert72 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert72_valid : cert72.Valid (canonical false ![1,3,2]) := by
  decide +kernel
lemma case72 : ForestBound (canonical false ![1,3,2]) := CycleForestCertificate.Data.forestBound cert72_valid
def cert73 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,9,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert73_valid : cert73.Valid (canonical false ![1,3,3]) := by
  decide +kernel
lemma case73 : ForestBound (canonical false ![1,3,3]) := CycleForestCertificate.Data.forestBound cert73_valid
def cert74 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,9,9,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert74_valid : cert74.Valid (canonical false ![1,3,4]) := by
  decide +kernel
lemma case74 : ForestBound (canonical false ![1,3,4]) := CycleForestCertificate.Data.forestBound cert74_valid
def cert75 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,9,9,9,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert75_valid : cert75.Valid (canonical false ![1,3,5]) := by
  decide +kernel
lemma case75 : ForestBound (canonical false ![1,3,5]) := CycleForestCertificate.Data.forestBound cert75_valid
def cert76 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 5),(Sum.inr (1,2)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,7,0,0,0],![5,7,9,9,9,9]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert76_valid : cert76.Valid (canonical false ![1,3,6]) := by
  decide +kernel
lemma case76 : ForestBound (canonical false ![1,3,6]) := CycleForestCertificate.Data.forestBound cert76_valid

end Erdos184Work.ChainRing
