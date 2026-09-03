import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert7 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,0,0,2,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),none,none,some (Sum.inr (1,0)),none] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert7_valid : cert7.Valid (canonical false ![0,1,0]) := by
  decide +kernel
lemma case7 : ForestBound (canonical false ![0,1,0]) := CycleForestCertificate.Data.forestBound cert7_valid
def cert8 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,2,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![3,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,0)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert8_valid : cert8.Valid (canonical false ![0,1,1]) := by
  decide +kernel
lemma case8 : ForestBound (canonical false ![0,1,1]) := CycleForestCertificate.Data.forestBound cert8_valid
def cert9 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,2,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![3,5,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert9_valid : cert9.Valid (canonical false ![0,1,2]) := by
  decide +kernel
lemma case9 : ForestBound (canonical false ![0,1,2]) := CycleForestCertificate.Data.forestBound cert9_valid
def cert10 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,2,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![3,5,7,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert10_valid : cert10.Valid (canonical false ![0,1,3]) := by
  decide +kernel
lemma case10 : ForestBound (canonical false ![0,1,3]) := CycleForestCertificate.Data.forestBound cert10_valid
def cert11 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 5),(Sum.inr (1,0)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,2,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![3,5,7,7,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert11_valid : cert11.Valid (canonical false ![0,1,4]) := by
  decide +kernel
lemma case11 : ForestBound (canonical false ![0,1,4]) := CycleForestCertificate.Data.forestBound cert11_valid
def cert12 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,2,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![3,5,7,7,7,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert12_valid : cert12.Valid (canonical false ![0,1,5]) := by
  decide +kernel
lemma case12 : ForestBound (canonical false ![0,1,5]) := CycleForestCertificate.Data.forestBound cert12_valid
def cert13 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 1),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 5),(Sum.inr (1,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 5),(Sum.inr (1,0)))}
  rank := fun | .inl h => ![0,0,2,4,0,2,6] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,0,0,0,0,0],![3,5,7,7,7,7]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,some (Sum.inr (1,0)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert13_valid : cert13.Valid (canonical false ![0,1,6]) := by
  decide +kernel
lemma case13 : ForestBound (canonical false ![0,1,6]) := CycleForestCertificate.Data.forestBound cert13_valid

end Erdos184Work.ChainRing
