import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert63 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,0,2,6,0] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),none,some (Sum.inr (0,0)),some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![none,none,none,none,none,none]] i j
lemma cert63_valid : cert63.Valid (canonical false ![1,2,0]) := by
  decide +kernel
lemma case63 : ForestBound (canonical false ![1,2,0]) := CycleForestCertificate.Data.forestBound cert63_valid
def cert64 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,6] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),none,none,none,none,none]] i j
lemma cert64_valid : cert64.Valid (canonical false ![1,2,1]) := by
  decide +kernel
lemma case64 : ForestBound (canonical false ![1,2,1]) := CycleForestCertificate.Data.forestBound cert64_valid
def cert65 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),none,none,none,none]] i j
lemma cert65_valid : cert65.Valid (canonical false ![1,2,2]) := by
  decide +kernel
lemma case65 : ForestBound (canonical false ![1,2,2]) := CycleForestCertificate.Data.forestBound cert65_valid
def cert66 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,9,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),none,none,none]] i j
lemma cert66_valid : cert66.Valid (canonical false ![1,2,3]) := by
  decide +kernel
lemma case66 : ForestBound (canonical false ![1,2,3]) := CycleForestCertificate.Data.forestBound cert66_valid
def cert67 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,2)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,9,9,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert67_valid : cert67.Valid (canonical false ![1,2,4]) := by
  decide +kernel
lemma case67 : ForestBound (canonical false ![1,2,4]) := CycleForestCertificate.Data.forestBound cert67_valid
def cert68 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 3),(Sum.inr (2,4)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,9,9,9,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert68_valid : cert68.Valid (canonical false ![1,2,5]) := by
  decide +kernel
lemma case68 : ForestBound (canonical false ![1,2,5]) := CycleForestCertificate.Data.forestBound cert68_valid
def cert69 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 3),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 3),(Sum.inr (2,4))),s((Sum.inl 3),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (0,0)))},{s((Sum.inl 1),(Sum.inr (0,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 3),(Sum.inr (2,0)))},{s((Sum.inl 3),(Sum.inr (2,3)))},{s((Sum.inl 4),(Sum.inr (0,0)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (0,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,0))),s((Sum.inl 3),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5))),s((Sum.inl 4),(Sum.inr (0,0)))}
  rank := fun | .inl h => ![0,2,4,6,2,6,8] h | .inr (i,j) => ![![1,0,0,0,0,0],![3,5,0,0,0,0],![5,7,9,9,9,9]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (0,0)),some (Sum.inr (1,0)),some (Sum.inr (2,0)),some (Sum.inr (0,0)),some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![some (Sum.inl 0),none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),none,none,none,none],![some (Sum.inl 2),some (Sum.inl 3),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert69_valid : cert69.Valid (canonical false ![1,2,6]) := by
  decide +kernel
lemma case69 : ForestBound (canonical false ![1,2,6]) := CycleForestCertificate.Data.forestBound cert69_valid

end Erdos184Work.ChainRing
