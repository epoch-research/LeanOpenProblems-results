import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert14 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1)))}
  rank := fun | .inl h => ![0,0,2,0,0,4,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),none,none,some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert14_valid : cert14.Valid (canonical false ![0,2,0]) := by
  decide +kernel
lemma case14 : ForestBound (canonical false ![0,2,0]) := CycleForestCertificate.Data.forestBound cert14_valid
def cert15 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![3,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert15_valid : cert15.Valid (canonical false ![0,2,1]) := by
  decide +kernel
lemma case15 : ForestBound (canonical false ![0,2,1]) := CycleForestCertificate.Data.forestBound cert15_valid
def cert16 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![3,5,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert16_valid : cert16.Valid (canonical false ![0,2,2]) := by
  decide +kernel
lemma case16 : ForestBound (canonical false ![0,2,2]) := CycleForestCertificate.Data.forestBound cert16_valid
def cert17 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![3,5,7,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert17_valid : cert17.Valid (canonical false ![0,2,3]) := by
  decide +kernel
lemma case17 : ForestBound (canonical false ![0,2,3]) := CycleForestCertificate.Data.forestBound cert17_valid
def cert18 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![3,5,7,7,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert18_valid : cert18.Valid (canonical false ![0,2,4]) := by
  decide +kernel
lemma case18 : ForestBound (canonical false ![0,2,4]) := CycleForestCertificate.Data.forestBound cert18_valid
def cert19 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![3,5,7,7,7,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert19_valid : cert19.Valid (canonical false ![0,2,5]) := by
  decide +kernel
lemma case19 : ForestBound (canonical false ![0,2,5]) := CycleForestCertificate.Data.forestBound cert19_valid
def cert20 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,0,2,4,0,4,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,0,0,0,0],![3,5,7,7,7,7]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert20_valid : cert20.Valid (canonical false ![0,2,6]) := by
  decide +kernel
lemma case20 : ForestBound (canonical false ![0,2,6]) := CycleForestCertificate.Data.forestBound cert20_valid

end Erdos184Work.ChainRing
