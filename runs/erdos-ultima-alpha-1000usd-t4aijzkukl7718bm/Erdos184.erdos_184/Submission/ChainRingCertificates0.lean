import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert0 : CycleForestCertificate.Data Vertex where
  pieces := ∅
  forest := ∅
  rank := fun | .inl h => ![0,0,0,0,0,0,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,none,none,none,none,none] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert0_valid : cert0.Valid (canonical false ![0,0,0]) := by
  decide +kernel
lemma case0 : ForestBound (canonical false ![0,0,0]) := CycleForestCertificate.Data.forestBound cert0_valid
def cert1 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,0,0,2,0,0,2] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,none,some (Sum.inr (2,0)),none,none,some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert1_valid : cert1.Valid (canonical false ![0,0,1]) := by
  decide +kernel
lemma case1 : ForestBound (canonical false ![0,0,1]) := CycleForestCertificate.Data.forestBound cert1_valid
def cert2 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))}}
  forest := {s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,0,0,2,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,none,some (Sum.inr (2,0)),none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert2_valid : cert2.Valid (canonical false ![0,0,2]) := by
  decide +kernel
lemma case2 : ForestBound (canonical false ![0,0,2]) := CycleForestCertificate.Data.forestBound cert2_valid
def cert3 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,0,0,2,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,none,none,some (Sum.inr (2,0)),none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert3_valid : cert3.Valid (canonical false ![0,0,3]) := by
  decide +kernel
lemma case3 : ForestBound (canonical false ![0,0,3]) := CycleForestCertificate.Data.forestBound cert3_valid
def cert4 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))}}
  forest := {s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,0,0,2,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,none,none,some (Sum.inr (2,0)),none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert4_valid : cert4.Valid (canonical false ![0,0,4]) := by
  decide +kernel
lemma case4 : ForestBound (canonical false ![0,0,4]) := CycleForestCertificate.Data.forestBound cert4_valid
def cert5 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,0,0,2,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,none,none,some (Sum.inr (2,0)),none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert5_valid : cert5.Valid (canonical false ![0,0,5]) := by
  decide +kernel
lemma case5 : ForestBound (canonical false ![0,0,5]) := CycleForestCertificate.Data.forestBound cert5_valid
def cert6 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,0,0,2,0,0,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![0,0,0,0,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,none,none,some (Sum.inr (2,0)),none,none,some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert6_valid : cert6.Valid (canonical false ![0,0,6]) := by
  decide +kernel
lemma case6 : ForestBound (canonical false ![0,0,6]) := CycleForestCertificate.Data.forestBound cert6_valid

end Erdos184Work.ChainRing
