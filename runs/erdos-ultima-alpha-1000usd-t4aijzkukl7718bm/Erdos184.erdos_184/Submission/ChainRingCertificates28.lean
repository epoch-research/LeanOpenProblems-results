import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert196 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))}
  rank := fun | .inl h => ![0,2,0,0,4,0,0] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,none,some (Sum.inr (0,1)),none,none] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert196_valid : cert196.Valid (canonical false ![4,0,0]) := by
  decide +kernel
lemma case196 : ForestBound (canonical false ![4,0,0]) := CycleForestCertificate.Data.forestBound cert196_valid
def cert197 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,2,0,2,4,0,2] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0)),some (Sum.inr (0,1)),none,some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert197_valid : cert197.Valid (canonical false ![4,0,1]) := by
  decide +kernel
lemma case197 : ForestBound (canonical false ![4,0,1]) := CycleForestCertificate.Data.forestBound cert197_valid
def cert198 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,2,0,2,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0)),some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert198_valid : cert198.Valid (canonical false ![4,0,2]) := by
  decide +kernel
lemma case198 : ForestBound (canonical false ![4,0,2]) := CycleForestCertificate.Data.forestBound cert198_valid
def cert199 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,2,0,2,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0)),some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert199_valid : cert199.Valid (canonical false ![4,0,3]) := by
  decide +kernel
lemma case199 : ForestBound (canonical false ![4,0,3]) := CycleForestCertificate.Data.forestBound cert199_valid
def cert200 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,2,0,2,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0)),some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert200_valid : cert200.Valid (canonical false ![4,0,4]) := by
  decide +kernel
lemma case200 : ForestBound (canonical false ![4,0,4]) := CycleForestCertificate.Data.forestBound cert200_valid
def cert201 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,2,0,2,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0)),some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert201_valid : cert201.Valid (canonical false ![4,0,5]) := by
  decide +kernel
lemma case201 : ForestBound (canonical false ![4,0,5]) := CycleForestCertificate.Data.forestBound cert201_valid
def cert202 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 0),(Sum.inr (0,3))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,2)))},{s((Sum.inl 1),(Sum.inr (0,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,2,0,2,4,0,4] h | .inr (i,j) => ![![1,3,5,5,0,0],![0,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),none,some (Sum.inr (2,0)),some (Sum.inr (0,1)),none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),some (Sum.inl 4),none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert202_valid : cert202.Valid (canonical false ![4,0,6]) := by
  decide +kernel
lemma case202 : ForestBound (canonical false ![4,0,6]) := CycleForestCertificate.Data.forestBound cert202_valid

end Erdos184Work.ChainRing
