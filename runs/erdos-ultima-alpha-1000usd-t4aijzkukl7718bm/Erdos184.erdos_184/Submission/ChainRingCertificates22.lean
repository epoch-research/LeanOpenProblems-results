import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert154 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,0,4,4,0] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,1)),some (Sum.inr (1,0)),none] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert154_valid : cert154.Valid (canonical false ![3,1,0]) := by
  decide +kernel
lemma case154 : ForestBound (canonical false ![3,1,0]) := CycleForestCertificate.Data.forestBound cert154_valid
def cert155 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,6,4,4,6] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![5,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert155_valid : cert155.Valid (canonical false ![3,1,1]) := by
  decide +kernel
lemma case155 : ForestBound (canonical false ![3,1,1]) := CycleForestCertificate.Data.forestBound cert155_valid
def cert156 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,6,4,4,8] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![5,7,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert156_valid : cert156.Valid (canonical false ![3,1,2]) := by
  decide +kernel
lemma case156 : ForestBound (canonical false ![3,1,2]) := CycleForestCertificate.Data.forestBound cert156_valid
def cert157 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,6,4,4,8] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![5,7,9,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert157_valid : cert157.Valid (canonical false ![3,1,3]) := by
  decide +kernel
lemma case157 : ForestBound (canonical false ![3,1,3]) := CycleForestCertificate.Data.forestBound cert157_valid
def cert158 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,6,4,4,8] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![5,7,9,9,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert158_valid : cert158.Valid (canonical false ![3,1,4]) := by
  decide +kernel
lemma case158 : ForestBound (canonical false ![3,1,4]) := CycleForestCertificate.Data.forestBound cert158_valid
def cert159 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,6,4,4,8] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![5,7,9,9,9,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert159_valid : cert159.Valid (canonical false ![3,1,5]) := by
  decide +kernel
lemma case159 : ForestBound (canonical false ![3,1,5]) := CycleForestCertificate.Data.forestBound cert159_valid
def cert160 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 0),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 1),(Sum.inr (0,2))),s((Sum.inl 4),(Sum.inr (0,0))),s((Sum.inl 4),(Sum.inr (0,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,1)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,2)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,1))),s((Sum.inl 4),(Sum.inr (0,2))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,2,4,6,4,4,8] h | .inr (i,j) => ![![1,3,5,0,0,0],![3,0,0,0,0,0],![5,7,9,9,9,9]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,1)),some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),some (Sum.inl 1),some (Sum.inl 4),none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert160_valid : cert160.Valid (canonical false ![3,1,6]) := by
  decide +kernel
lemma case160 : ForestBound (canonical false ![3,1,6]) := CycleForestCertificate.Data.forestBound cert160_valid

end Erdos184Work.ChainRing
