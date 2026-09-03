import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert28 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))}
  rank := fun | .inl h => ![0,0,2,0,0,4,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),none,none,some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![none,none,none,none,none,none]] i j
lemma cert28_valid : cert28.Valid (canonical false ![0,4,0]) := by
  decide +kernel
lemma case28 : ForestBound (canonical false ![0,4,0]) := CycleForestCertificate.Data.forestBound cert28_valid
def cert29 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![3,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert29_valid : cert29.Valid (canonical false ![0,4,1]) := by
  decide +kernel
lemma case29 : ForestBound (canonical false ![0,4,1]) := CycleForestCertificate.Data.forestBound cert29_valid
def cert30 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![3,5,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert30_valid : cert30.Valid (canonical false ![0,4,2]) := by
  decide +kernel
lemma case30 : ForestBound (canonical false ![0,4,2]) := CycleForestCertificate.Data.forestBound cert30_valid
def cert31 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![3,5,7,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert31_valid : cert31.Valid (canonical false ![0,4,3]) := by
  decide +kernel
lemma case31 : ForestBound (canonical false ![0,4,3]) := CycleForestCertificate.Data.forestBound cert31_valid
def cert32 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![3,5,7,7,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert32_valid : cert32.Valid (canonical false ![0,4,4]) := by
  decide +kernel
lemma case32 : ForestBound (canonical false ![0,4,4]) := CycleForestCertificate.Data.forestBound cert32_valid
def cert33 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![3,5,7,7,7,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert33_valid : cert33.Valid (canonical false ![0,4,5]) := by
  decide +kernel
lemma case33 : ForestBound (canonical false ![0,4,5]) := CycleForestCertificate.Data.forestBound cert33_valid
def cert34 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![3,5,7,7,7,7]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert34_valid : cert34.Valid (canonical false ![0,4,6]) := by
  decide +kernel
lemma case34 : ForestBound (canonical false ![0,4,6]) := CycleForestCertificate.Data.forestBound cert34_valid

end Erdos184Work.ChainRing
