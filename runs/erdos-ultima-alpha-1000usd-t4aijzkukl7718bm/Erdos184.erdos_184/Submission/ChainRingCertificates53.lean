import Submission.ChainRingDefinitions
/-! Finite cycle-and-forest certificates for canonical active subgraphs. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
set_option Elab.async false
def cert371 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))}}
  forest := {s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 2),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))}
  rank := fun | .inl h => ![0,0,2,0,0,4,0] h | .inr (i,j) => ![![0,0,0,0,0,0],![1,3,5,5,0,0],![0,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,none,some (Sum.inr (1,0)),none,none,some (Sum.inr (1,1)),none] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 1),some (Sum.inl 2),some (Sum.inl 5),some (Sum.inl 5),none,none],![none,none,none,none,none,none]] i j
lemma cert371_valid : cert371.Valid (canonical true ![0,4,0]) := by
  decide +kernel
lemma case371 : ForestBound (canonical true ![0,4,0]) := CycleForestCertificate.Data.forestBound cert371_valid
def cert372 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0)))},{s((Sum.inl 6),(Sum.inr (2,0)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 6),(Sum.inr (2,0)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,2] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,7,7,0,0],![1,0,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,0))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 0),none,none,none,none,none]] i j
lemma cert372_valid : cert372.Valid (canonical true ![0,4,1]) := by
  decide +kernel
lemma case372 : ForestBound (canonical true ![0,4,1]) := CycleForestCertificate.Data.forestBound cert372_valid
def cert373 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,7,7,0,0],![1,3,0,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 0),some (Sum.inl 2),none,none,none,none]] i j
lemma cert373_valid : cert373.Valid (canonical true ![0,4,2]) := by
  decide +kernel
lemma case373 : ForestBound (canonical true ![0,4,2]) := CycleForestCertificate.Data.forestBound cert373_valid
def cert374 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,7,7,0,0],![1,3,5,0,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),none,none,none]] i j
lemma cert374_valid : cert374.Valid (canonical true ![0,4,3]) := by
  decide +kernel
lemma case374 : ForestBound (canonical true ![0,4,3]) := CycleForestCertificate.Data.forestBound cert374_valid
def cert375 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,2)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,7,7,0,0],![1,3,5,5,0,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),none,none]] i j
lemma cert375_valid : cert375.Valid (canonical true ![0,4,4]) := by
  decide +kernel
lemma case375 : ForestBound (canonical true ![0,4,4]) := CycleForestCertificate.Data.forestBound cert375_valid
def cert376 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 0),(Sum.inr (2,4)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 6),(Sum.inr (2,2)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,7,7,0,0],![1,3,5,5,5,0]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),none]] i j
lemma cert376_valid : cert376.Valid (canonical true ![0,4,5]) := by
  decide +kernel
lemma case376 : ForestBound (canonical true ![0,4,5]) := CycleForestCertificate.Data.forestBound cert376_valid
def cert377 : CycleForestCertificate.Data Vertex where
  pieces := {{s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,0))),s((Sum.inl 5),(Sum.inr (1,1)))},{s((Sum.inl 1),(Sum.inr (1,2))),s((Sum.inl 1),(Sum.inr (1,3))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3)))},{s((Sum.inl 0),(Sum.inr (2,1))),s((Sum.inl 0),(Sum.inr (2,2))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,0))),s((Sum.inl 6),(Sum.inr (2,1)))},{s((Sum.inl 0),(Sum.inr (2,4))),s((Sum.inl 0),(Sum.inr (2,5))),s((Sum.inl 2),(Sum.inr (2,3))),s((Sum.inl 2),(Sum.inr (2,5))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4)))},{s((Sum.inl 0),(Sum.inr (2,0)))},{s((Sum.inl 0),(Sum.inr (2,3)))},{s((Sum.inl 2),(Sum.inr (1,0)))},{s((Sum.inl 2),(Sum.inr (1,1)))},{s((Sum.inl 2),(Sum.inr (1,2)))},{s((Sum.inl 2),(Sum.inr (1,3)))},{s((Sum.inl 2),(Sum.inr (2,1)))},{s((Sum.inl 2),(Sum.inr (2,4)))},{s((Sum.inl 6),(Sum.inr (2,2)))},{s((Sum.inl 6),(Sum.inr (2,5)))}}
  forest := {s((Sum.inl 0),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (2,0))),s((Sum.inl 2),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,0))),s((Sum.inl 1),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,1))),s((Sum.inl 5),(Sum.inr (1,2))),s((Sum.inl 5),(Sum.inr (1,3))),s((Sum.inl 2),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,1))),s((Sum.inl 6),(Sum.inr (2,2))),s((Sum.inl 6),(Sum.inr (2,3))),s((Sum.inl 6),(Sum.inr (2,4))),s((Sum.inl 6),(Sum.inr (2,5)))}
  rank := fun | .inl h => ![0,4,2,0,0,6,4] h | .inr (i,j) => ![![0,0,0,0,0,0],![3,5,7,7,0,0],![1,3,5,5,5,5]] i j
  parent := fun | .inl h => ![none,some (Sum.inr (1,0)),some (Sum.inr (2,0)),none,none,some (Sum.inr (1,1)),some (Sum.inr (2,1))] h | .inr (i,j) => ![![none,none,none,none,none,none],![some (Sum.inl 2),some (Sum.inl 1),some (Sum.inl 5),some (Sum.inl 5),none,none],![some (Sum.inl 0),some (Sum.inl 2),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6),some (Sum.inl 6)]] i j
lemma cert377_valid : cert377.Valid (canonical true ![0,4,6]) := by
  decide +kernel
lemma case377 : ForestBound (canonical true ![0,4,6]) := CycleForestCertificate.Data.forestBound cert377_valid

end Erdos184Work.ChainRing
